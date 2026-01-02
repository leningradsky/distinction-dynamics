#!/bin/bash

# Distinction Dynamics - Compile All Modules
# Usage: ./compile.sh [--check-only]

set -e

MODULES=(
    "S3toSO3"
    "TriadSU2"
    "TriadToSU2"
    "SpinorPhysics"
    "Electroweak"
    "Delta4Invariants"
    "Gravity"
    "QuantumMechanics"
    "ParticleMasses"
    "Maxwell"
    "Thermodynamics"
    "Dirac"
    "QED"
    "QCD"
    "Cosmology"
    "StandardModel"
    "DistinctionDynamics"
)

CHECK_ONLY=""
if [ "$1" == "--check-only" ]; then
    CHECK_ONLY="--only-scope-checking"
    echo "=== Scope checking only ==="
fi

echo "=== Distinction Dynamics - Agda Compilation ==="
echo ""

PASSED=0
FAILED=0

for module in "${MODULES[@]}"; do
    echo -n "Checking $module.agda ... "
    if agda --safe $CHECK_ONLY "$module.agda" 2>/dev/null; then
        echo "OK"
        ((PASSED++))
    else
        echo "FAILED"
        ((FAILED++))
    fi
done

echo ""
echo "=== Summary ==="
echo "Passed: $PASSED"
echo "Failed: $FAILED"
echo "Total:  ${#MODULES[@]}"

if [ $FAILED -eq 0 ]; then
    echo ""
    echo "All modules verified successfully!"
    exit 0
else
    echo ""
    echo "Some modules failed verification."
    exit 1
fi
