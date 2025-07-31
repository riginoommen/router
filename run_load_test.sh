#!/bin/bash

# Script to run Apollo Router with drill load testing
set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Configuration
ROUTER_PORT=4000
OTEL_COLLECTOR_PORT=4318
OTEL_GRPC_PORT=4317
ROUTER_PID_FILE="/tmp/router.pid"
DRILL_CONFIG="drill.yml"
SUPERGRAPH_SCHEMA="supergraph.graphql"
COLLECTOR_CONFIG="collector.yaml"
OTEL_CONTAINER_NAME="otel-collector-loadtest"
TEST_RUN_ID="loadtest-$(date +%Y%m%d-%H%M%S)-$$"

# Function to print colored output
print_status() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

print_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

print_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Function to cleanup on exit
cleanup() {
    print_status "Cleaning up..."
    
    # Stop router
    if [ -f "$ROUTER_PID_FILE" ]; then
        ROUTER_PID=$(cat "$ROUTER_PID_FILE")
        if kill -0 "$ROUTER_PID" 2>/dev/null; then
            print_status "Stopping router (PID: $ROUTER_PID)"
            kill "$ROUTER_PID"
            rm -f "$ROUTER_PID_FILE"
        fi
    fi
    
    # Stop OpenTelemetry collector container
    if docker ps --format "table {{.Names}}" | grep -q "$OTEL_CONTAINER_NAME"; then
        print_status "Stopping OpenTelemetry collector container"
        docker stop "$OTEL_CONTAINER_NAME" >/dev/null 2>&1
        docker rm "$OTEL_CONTAINER_NAME" >/dev/null 2>&1
    fi
}

# Set up cleanup trap
trap cleanup EXIT INT TERM

# Function to check if command exists
command_exists() {
    command -v "$1" >/dev/null 2>&1
}

# Check prerequisites
print_status "Checking prerequisites..."

if ! command_exists "cargo"; then
    print_error "cargo not found - please install Rust"
    exit 1
fi

if ! command_exists "drill"; then
    print_error "drill not found - please install drill: cargo install drill"
    print_status "Installing drill..."
    cargo install drill
fi

if ! command_exists "docker"; then
    print_error "docker not found - please install Docker"
    exit 1
fi

if [ ! -f "$SUPERGRAPH_SCHEMA" ]; then
    print_error "Supergraph schema not found at $SUPERGRAPH_SCHEMA"
    exit 1
fi

if [ ! -f "$DRILL_CONFIG" ]; then
    print_error "Drill config not found at $DRILL_CONFIG"
    exit 1
fi

if [ ! -f "$COLLECTOR_CONFIG" ]; then
    print_error "OpenTelemetry collector config not found at $COLLECTOR_CONFIG"
    exit 1
fi

print_success "Prerequisites check passed"

# Start OpenTelemetry collector
print_status "Starting OpenTelemetry collector with test run ID: $TEST_RUN_ID"

# Stop any existing container with the same name
docker stop "$OTEL_CONTAINER_NAME" >/dev/null 2>&1 || true
docker rm "$OTEL_CONTAINER_NAME" >/dev/null 2>&1 || true

# Start the OpenTelemetry collector container
docker run -d \
    --name "$OTEL_CONTAINER_NAME" \
    -p $OTEL_GRPC_PORT:4317 \
    -p $OTEL_COLLECTOR_PORT:4318 \
    -p 8889:8889 \
    -p 8888:8888 \
    -e DD_API_KEY="${DD_API_KEY:-}" \
    -e TEST_RUN_ID="${TEST_RUN_ID}" \
    -e USER="${USER}" \
    -v "$(pwd)/$COLLECTOR_CONFIG:/etc/otelcol-contrib/otel-collector-config.yaml" \
    -v "$(pwd):/workspace" \
    -w /workspace \
    otel/opentelemetry-collector-contrib:latest \
    --config=/etc/otelcol-contrib/otel-collector-config.yaml

if [ $? -eq 0 ]; then
    print_success "OpenTelemetry collector started"
else
    print_error "Failed to start OpenTelemetry collector"
    exit 1
fi

# Wait for collector to be ready
print_status "Waiting for OpenTelemetry collector to be ready..."
for i in {1..10}; do
    if curl -s "http://localhost:8888/metrics" >/dev/null 2>&1; then
        print_success "OpenTelemetry collector is ready!"
        break
    fi
    if [ $i -eq 10 ]; then
        print_warning "OpenTelemetry collector may not be fully ready, but continuing..."
        print_status "OpenTelemetry collector logs:"
        docker logs "$OTEL_CONTAINER_NAME" --tail 20
    fi
    sleep 2
done

# Show initial collector logs
print_status "OpenTelemetry collector startup logs:"
docker logs "$OTEL_CONTAINER_NAME" --tail 10

# Build the router
print_status "Building Apollo Router..."
if ! cargo build --release; then
    print_error "Failed to build router"
    exit 1
fi
print_success "Router built successfully"

# Start the router
print_status "Starting Apollo Router on port $ROUTER_PORT..."

# Start router in background
cargo run --release -- --config router.yaml --supergraph supergraph-massive.graphql --hot-reload --dev &
ROUTER_PID=$!
echo $ROUTER_PID > "$ROUTER_PID_FILE"

print_status "Router started with PID: $ROUTER_PID"

# Wait for router to be ready
print_status "Waiting for router to be ready..."
for i in {1..30}; do
    if curl -s "http://localhost:$ROUTER_PORT" >/dev/null 2>&1; then
        print_success "Router is ready!"
        break
    fi
    if [ $i -eq 30 ]; then
        print_error "Router failed to start within 30 seconds"
        exit 1
    fi
    sleep 1
done

# Test router health
print_status "Testing router health..."
if curl -s -f "http://localhost:$ROUTER_PORT/.well-known/apollo/server-health" >/dev/null; then
    print_success "Router health check passed"
else
    print_warning "Router health check failed, but continuing with load test"
fi

# Run drill load test
print_status "Starting drill load test..."
print_status "Configuration: $DRILL_CONFIG"
print_status "Target: http://localhost:$ROUTER_PORT"

echo
echo "=================================="
echo "    DRILL LOAD TEST STARTING"
echo "=================================="
echo

if drill --quiet --benchmark "$DRILL_CONFIG"; then
    print_success "Load test completed successfully"
    DRILL_SUCCESS=true
else
    print_error "Load test failed"
    DRILL_SUCCESS=false
fi

echo
echo "=================================="
echo "    LOAD TEST COMPLETED"  
echo "=================================="
echo

print_status "Load test finished. Test Run ID: $TEST_RUN_ID"

if [ "$DRILL_SUCCESS" = true ]; then
    print_success "Drill test completed successfully"
else
    print_error "Drill test failed"
fi

echo
print_status "Final OpenTelemetry collector logs:"
docker logs "$OTEL_CONTAINER_NAME" --tail 10

echo
print_status "Cleaning up and shutting down services..."

# The cleanup function will be called automatically due to the trap
# This will stop both the router and collector

if [ "$DRILL_SUCCESS" = true ]; then
    exit 0
else
    exit 1
fi