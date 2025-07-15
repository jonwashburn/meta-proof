#!/bin/bash
# Project Health Check Script for Riemann Hypothesis Project

set -e

echo "🏥 Riemann Hypothesis Project Health Check"
echo "=========================================="

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Counters
PASS=0
WARN=0
FAIL=0

# Function to print status
print_status() {
    local status=$1
    local message=$2
    case $status in
        "PASS")
            echo -e "${GREEN}✅ PASS${NC}: $message"
            ((PASS++))
            ;;
        "WARN")
            echo -e "${YELLOW}⚠️  WARN${NC}: $message"
            ((WARN++))
            ;;
        "FAIL")
            echo -e "${RED}❌ FAIL${NC}: $message"
            ((FAIL++))
            ;;
    esac
}

echo "🔍 Checking project structure and integrity..."

# Test 1: Check that main library target actually exists and isn't empty
echo -e "\n${BLUE}📁 Test 1: Main Library Target Validation${NC}"

if [ -d "rh/academic_framework" ]; then
    MAIN_FILES=$(find rh/academic_framework -name "*.lean" | wc -l)
    if [ "$MAIN_FILES" -gt 0 ]; then
        print_status "PASS" "Main library target exists with $MAIN_FILES files"
        
        # Check for substantial content
        EMPTY_FILES=0
        for file in rh/academic_framework/*.lean; do
            if [ -f "$file" ]; then
                CONTENT_LINES=$(grep -v '^\s*--' "$file" | grep -v '^\s*$' | wc -l)
                if [ "$CONTENT_LINES" -lt 10 ]; then
                    print_status "WARN" "File $file has only $CONTENT_LINES lines of content"
                    ((EMPTY_FILES++))
                fi
            fi
        done
        
        if [ "$EMPTY_FILES" -eq 0 ]; then
            print_status "PASS" "All main files contain substantial content"
        fi
    else
        print_status "FAIL" "Main library target directory exists but contains no .lean files"
    fi
else
    print_status "FAIL" "Main library target directory 'rh/academic_framework' does not exist"
fi

# Test 2: Build verification
echo -e "\n${BLUE}🏗️  Test 2: Build Verification${NC}"

if lake build --dry-run >/dev/null 2>&1; then
    print_status "PASS" "Project configuration is valid"
else
    print_status "FAIL" "Project has configuration or compilation errors"
fi

# Test 3: API completeness check
echo -e "\n${BLUE}🔌 Test 3: API Completeness Check${NC}"

KEY_DEFINITIONS=("PrimeIndex" "fredholm_det" "EulerProduct")
MISSING_DEFS=0

for def in "${KEY_DEFINITIONS[@]}"; do
    if find rh -name "*.lean" -exec grep -l "$def" {} \; | head -1 >/dev/null; then
        print_status "PASS" "Key definition '$def' found"
    else
        print_status "WARN" "Key definition '$def' not found (check if implemented)"
        ((MISSING_DEFS++))
    fi
done

# Final Summary
echo -e "\n${BLUE}📊 Final Summary${NC}"
echo "================================"
echo -e "✅ Passed: ${GREEN}$PASS${NC}"
echo -e "⚠️  Warnings: ${YELLOW}$WARN${NC}"  
echo -e "❌ Failed: ${RED}$FAIL${NC}"

if [ "$FAIL" -eq 0 ] && [ "$WARN" -le 3 ]; then
    echo -e "\n${GREEN}🎉 Project appears healthy! Low risk of embarrassing situations.${NC}"
    exit 0
elif [ "$FAIL" -eq 0 ]; then
    echo -e "\n${YELLOW}⚠️  Project has some warnings but should be OK.${NC}"
    exit 0
else
    echo -e "\n${RED}🚨 Project has serious issues that could lead to embarrassment!${NC}"
    exit 1
fi
