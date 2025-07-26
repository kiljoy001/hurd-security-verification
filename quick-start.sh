#!/bin/bash
# Quick Start Script for GNU Hurd Security Verification Project
# This script helps developers quickly verify and test the project

set -e

echo "GNU Hurd Security Verification - Quick Start"
echo "============================================"
echo ""

# Check prerequisites
echo "Checking prerequisites..."
command -v coqc >/dev/null 2>&1 || { echo "Error: Coq not found. Please install: sudo apt-get install coq"; exit 1; }
command -v gcc >/dev/null 2>&1 || { echo "Error: GCC not found. Please install: sudo apt-get install gcc"; exit 1; }
command -v make >/dev/null 2>&1 || { echo "Error: Make not found. Please install: sudo apt-get install make"; exit 1; }
echo "✓ All prerequisites found"
echo ""

# Verify Coq proofs
echo "1. Verifying formal Coq proofs..."
cd coq/
if make verify > /dev/null 2>&1; then
    echo "✓ All Coq proofs verified (0 admits)"
else
    echo "✗ Coq verification failed"
    exit 1
fi
cd ..
echo ""

# Build ULE scheduler
echo "2. Building ULE scheduler..."
cd coq/
if make clean all > /dev/null 2>&1; then
    echo "✓ ULE scheduler built successfully"
else
    echo "✗ ULE scheduler build failed"
    exit 1
fi
cd ..
echo ""

# Test kernel patches
echo "3. Testing kernel security patches..."
cd kernel-patches/
if make test > /dev/null 2>&1; then
    echo "✓ All kernel patch tests passed (100%)"
else
    echo "✗ Kernel patch tests failed"
    exit 1
fi
cd ..
echo ""

# Summary
echo "============================================"
echo "Quick Start Complete!"
echo ""
echo "Key Results:"
echo "- Formal Coq proofs: VERIFIED (0 admits)"
echo "- ULE scheduler: BUILT"
echo "- Security patches: TESTED (100% pass)"
echo ""
echo "Next Steps:"
echo "1. Review the comprehensive report: GNU_Hurd_Security_Report.pdf"
echo "2. Check ULE scheduler docs: coq/ULE_SCHEDULER_README.md"
echo "3. Examine kernel patches: kernel-patches/mach-port-rights-fix.patch"
echo ""
echo "For integration with GNU Hurd, see the README.md"
echo "============================================"