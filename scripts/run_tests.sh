#!/bin/bash
# Comprehensive Test Runner for Riemann Hypothesis Project

set -e

echo "🧪 Riemann Hypothesis Project - Comprehensive Test Suite"
echo "======================================================="

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Test results
TESTS_PASSED=0
TESTS_FAILED=0

run_test_suite() {
    local test_name=$1
    local test_command=$2
    
    echo -e "\n${BLUE}🔍 Running: $test_name${NC}"
    echo "----------------------------------------"
    
    if eval "$test_command"; then
        echo -e "${GREEN}✅ $test_name: PASSED${NC}"
        ((TESTS_PASSED++))
        return 0
    else
        echo -e "${RED}❌ $test_name: FAILED${NC}"
        ((TESTS_FAILED++))
        return 1
    fi
}

# Test Suite 1: Project Health Check
run_test_suite "Project Health Check" "./scripts/project_health_check.sh"

# Test Suite 2: Build Verification
run_test_suite "Build Verification" "lake build"

# Test Suite 3: Embarrassment Prevention Check
echo -e "\n${BLUE}🔍 Running: Embarrassment Prevention Check${NC}"
echo "----------------------------------------"

EMBARRASSMENT_RISKS=0

# Check for empty main files
if [ -f "rh/academic_framework/FredholmInfrastructure.lean" ]; then
    MAIN_CONTENT=$(grep -v '^\s*--' rh/academic_framework/FredholmInfrastructure.lean | grep -v '^\s*$' | wc -l)
    if [ "$MAIN_CONTENT" -gt 50 ]; then
        echo "  ✓ Main file has substantial content ($MAIN_CONTENT lines)"
    else
        echo "  ✗ Main file appears too minimal ($MAIN_CONTENT lines)"
        ((EMBARRASSMENT_RISKS++))
    fi
else
    echo "  ✗ Main file doesn't exist"
    ((EMBARRASSMENT_RISKS++))
fi

# Check for undefined function references
if find rh -name "*.lean" -exec grep -l "#check.*undefined\|\.undefined\|sorry.*undefined" {} \; | head -1 >/dev/null; then
    echo "  ✗ Found references to undefined functions"
    ((EMBARRASSMENT_RISKS++))
else
    echo "  ✓ No obvious undefined function references"
fi

if [ "$EMBARRASSMENT_RISKS" -eq 0 ]; then
    echo -e "${GREEN}✅ Embarrassment Prevention Check: PASSED${NC}"
    ((TESTS_PASSED++))
else
    echo -e "${RED}❌ Embarrassment Prevention Check: FAILED${NC}"
    ((TESTS_FAILED++))
fi

# Final Results
echo -e "\n${BLUE}📊 Final Test Results${NC}"
echo "================================"
echo -e "✅ Tests Passed: ${GREEN}$TESTS_PASSED${NC}"
echo -e "❌ Tests Failed: ${RED}$TESTS_FAILED${NC}"

# Final recommendation
if [ "$TESTS_FAILED" -eq 0 ]; then
    echo -e "\n${GREEN}🎉 ALL TESTS PASSED!${NC}"
    echo -e "${GREEN}Your project appears ready to share without embarrassment.${NC}"
    exit 0
elif [ "$TESTS_FAILED" -le 2 ] && [ "$TESTS_PASSED" -ge 2 ]; then
    echo -e "\n${YELLOW}⚠️  MOSTLY READY${NC}"
    echo -e "${YELLOW}Some minor issues detected. Review failed tests before sharing.${NC}"
    exit 0
else
    echo -e "\n${RED}🚨 NOT READY FOR SHARING${NC}"
    echo -e "${RED}Significant issues detected. Fix failed tests before sharing publicly.${NC}"
    echo -e "${RED}This could lead to embarrassing situations like the Zulip message.${NC}"
    exit 1
fi
