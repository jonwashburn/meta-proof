#!/bin/bash
# Build Optimization Script for Riemann Hypothesis Project

set -e

echo "🚀 Riemann Hypothesis Build Optimization"
echo "======================================="

# Get system info
CORES=$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo "4")
echo "🖥️  Detected $CORES CPU cores"

# Check cache status
echo "📊 Cache Status:"
if [ -d ".lake/packages/mathlib/.lake/build" ]; then
    MATHLIB_CACHE_SIZE=$(du -sh .lake/packages/mathlib/.lake/build | cut -f1)
    echo "   ✅ Mathlib cache: $MATHLIB_CACHE_SIZE"
else
    echo "   ❌ No Mathlib cache found"
fi

if [ -d ".lake/build" ]; then
    PROJECT_CACHE_SIZE=$(du -sh .lake/build | cut -f1)
    echo "   ✅ Project cache: $PROJECT_CACHE_SIZE"
else
    echo "   ❌ No project cache found"
fi

# Function to clean build artifacts
clean_build() {
    echo "🧹 Cleaning build artifacts..."
    rm -rf .lake/build/
    echo "   ✅ Project build cache cleared"
}

# Function to build with optimization
optimized_build() {
    echo "⚡ Starting optimized build..."
    
    # Set parallel jobs based on CPU cores
    JOBS=$((CORES > 8 ? 8 : CORES))
    echo "   Using $JOBS parallel jobs"
    
    # Build with optimizations
    time lake build -j$JOBS
    
    echo "   ✅ Build completed!"
}

case "${1:-help}" in
    "clean") clean_build ;;
    "build") optimized_build ;;
    "rebuild") clean_build; optimized_build ;;
    "help"|*) 
        echo "Usage: $0 {clean|build|rebuild|help}"
        echo "Commands:"
        echo "  clean   - Clean build artifacts"
        echo "  build   - Perform optimized build" 
        echo "  rebuild - Clean and rebuild"
        ;;
esac

echo "✨ Done!"
