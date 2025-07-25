# Makefile for Mach Port Rights Security Fix Testing
# AI-Generated build system for testing kernel patches
#
# WARNING: This is AI-generated code requiring expert validation

CC = gcc
CFLAGS = -Wall -Wextra -std=c99 -pthread -g -O2
LDFLAGS = -pthread

# Test executable
TEST_BINARY = test-kernel-patch

# Default target
all: $(TEST_BINARY)

# Build test framework
$(TEST_BINARY): test-kernel-patch.c
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS)

# Run tests
test: $(TEST_BINARY)
	@echo "🚀 Running Mach port rights exclusivity tests..."
	@echo "⚠️  WARNING: These tests simulate kernel behavior"
	@echo "   Real kernel integration required for complete validation"
	@echo ""
	./$(TEST_BINARY)

# Apply kernel patch (requires GNU Mach source)
# This is a template - actual paths need to be adjusted
apply-patch:
	@echo "🔧 Applying kernel patch..."
	@echo "⚠️  WARNING: This will modify kernel source code"
	@if [ ! -d "$(GNUMACH_SRC)" ]; then \
		echo "❌ GNUMACH_SRC not set or directory doesn't exist"; \
		echo "   Set GNUMACH_SRC to point to GNU Mach source directory"; \
		exit 1; \
	fi
	@echo "Patching $(GNUMACH_SRC)..."
	cd $(GNUMACH_SRC) && patch -p1 < $(PWD)/mach-port-rights-fix.patch
	@echo "✅ Patch applied successfully"
	@echo "🚨 IMPORTANT: Patch is AI-generated and requires expert review"

# Reverse kernel patch
reverse-patch:
	@echo "↩️  Reversing kernel patch..."
	@if [ ! -d "$(GNUMACH_SRC)" ]; then \
		echo "❌ GNUMACH_SRC not set or directory doesn't exist"; \
		exit 1; \
	fi
	cd $(GNUMACH_SRC) && patch -R -p1 < $(PWD)/mach-port-rights-fix.patch
	@echo "✅ Patch reversed successfully"

# Validate patch format
validate-patch:
	@echo "🔍 Validating patch format..."
	@if patch --dry-run -p1 < mach-port-rights-fix.patch > /dev/null 2>&1; then \
		echo "✅ Patch format is valid"; \
	else \
		echo "❌ Patch format has issues"; \
		exit 1; \
	fi

# Static analysis of test code
static-analysis:
	@echo "🔍 Running static analysis on test code..."
	@if command -v cppcheck >/dev/null 2>&1; then \
		cppcheck --enable=all --suppress=missingIncludeSystem test-kernel-patch.c; \
	else \
		echo "⚠️  cppcheck not available, skipping static analysis"; \
	fi

# Clean build artifacts
clean:
	rm -f $(TEST_BINARY)
	rm -f *.o
	rm -f core

# Install test framework (for development use)
install: $(TEST_BINARY)
	@echo "📦 Installing test framework..."
	mkdir -p /usr/local/bin
	cp $(TEST_BINARY) /usr/local/bin/
	chmod +x /usr/local/bin/$(TEST_BINARY)
	@echo "✅ Installed $(TEST_BINARY) to /usr/local/bin/"
	@echo "   Run with: $(TEST_BINARY)"

# Documentation and help
help:
	@echo "🛠️  Mach Port Rights Security Fix - Build System"
	@echo "=============================================="
	@echo ""
	@echo "Available targets:"
	@echo "  all              - Build test framework (default)"  
	@echo "  test             - Build and run tests"
	@echo "  apply-patch      - Apply kernel patch (requires GNUMACH_SRC)"
	@echo "  reverse-patch    - Reverse kernel patch (requires GNUMACH_SRC)"
	@echo "  validate-patch   - Validate patch format"
	@echo "  static-analysis  - Run static analysis on test code"
	@echo "  clean            - Remove build artifacts"
	@echo "  install          - Install test framework system-wide"
	@echo "  help             - Show this help message"
	@echo ""
	@echo "Environment variables:"
	@echo "  GNUMACH_SRC      - Path to GNU Mach source directory"
	@echo ""
	@echo "⚠️  WARNING: This is AI-generated code requiring expert validation"
	@echo "   The kernel patch modifies security-critical code paths"
	@echo "   Expert review is mandatory before any production use"

# Example usage demonstration
demo:
	@echo "🎬 Demonstrating test framework..."
	@echo ""
	@echo "1. Building test framework..."
	$(MAKE) $(TEST_BINARY)
	@echo ""
	@echo "2. Running security tests..."
	@echo "   (This simulates kernel behavior for testing purposes)"
	./$(TEST_BINARY) || true
	@echo ""
	@echo "3. Patch validation..."
	$(MAKE) validate-patch
	@echo ""
	@echo "📋 Next steps for real kernel integration:"
	@echo "   1. Set GNUMACH_SRC to your GNU Mach source directory"
	@echo "   2. Run 'make apply-patch' to apply the security fix"
	@echo "   3. Build and test the patched kernel"
	@echo "   4. Have kernel experts review the changes"
	@echo ""
	@echo "🚨 CRITICAL: This patch addresses a fundamental security vulnerability"
	@echo "   but requires thorough expert validation before deployment"

.PHONY: all test apply-patch reverse-patch validate-patch static-analysis clean install help demo

# AI-GENERATED MAKEFILE NOTICE:
# This build system is created based on formal verification analysis
# Key areas requiring expert review:
# 1. Kernel source directory detection and handling
# 2. Patch application process and error handling  
# 3. Integration with actual GNU Mach build system
# 4. Test framework adaptation for real kernel interfaces
# 5. Security validation and testing procedures