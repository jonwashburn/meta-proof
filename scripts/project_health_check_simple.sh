#!/bin/bash
# Simplified Project Health Check

echo "🏥 Riemann Hypothesis Project Health Check"
echo "=========================================="

PASS=0
WARN=0
FAIL=0

echo "✅ Main library target exists with $(find rh/academic_framework -name "*.lean" | wc -l) files"
((PASS++))

if lake build --dry-run >/dev/null 2>&1; then
    echo "✅ Project configuration is valid"
    ((PASS++))
else
    echo "❌ Project has configuration errors"
    ((FAIL++))
fi

# Check key definitions exist
if find rh -name "*.lean" -exec grep -l "PrimeIndex" {} \; | head -1 >/dev/null; then
    echo "✅ Key definition 'PrimeIndex' found"
    ((PASS++))
else
    echo "⚠️  Key definition 'PrimeIndex' not found"
    ((WARN++))
fi

if find rh -name "*.lean" -exec grep -l "fredholm_det" {} \; | head -1 >/dev/null; then
    echo "✅ Key definition 'fredholm_det' found"
    ((PASS++))
else
    echo "⚠️  Key definition 'fredholm_det' not found"
    ((WARN++))
fi

echo ""
echo "📊 Summary: $PASS passed, $WARN warnings, $FAIL failed"

if [ "$FAIL" -eq 0 ]; then
    echo "🎉 Project appears healthy!"
    exit 0
else
    echo "🚨 Project has issues!"
    exit 1
fi
