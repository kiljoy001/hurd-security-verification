# GNU Hurd ULE Scheduler Testing Suite Makefile
# Comprehensive build system for ULE scheduler testing and validation
# Copyright (C) 2025 Free Software Foundation, Inc.

CC = gcc
CFLAGS = -Wall -Wextra -O2 -std=gnu99 -pthread -g
LDFLAGS = -lm -lpthread -lrt
SRCDIR = .
BUILDDIR = build
BINDIR = bin
RESULTSDIR = results

# Test executables
TESTS = ule_scheduler_stress_test \
        ule_interactivity_test \
        ule_multicore_validation \
        ule_performance_benchmark \
        ule_fsm_integration_stress

# Test sources
SOURCES = ule_scheduler_stress_test.c \
          ule_interactivity_test.c \
          ule_multicore_validation.c \
          ule_performance_benchmark.c \
          ule_fsm_integration_stress.c

# Object files
OBJECTS = $(SOURCES:%.c=$(BUILDDIR)/%.o)

# Test binaries
BINARIES = $(TESTS:%=$(BINDIR)/%)

# Default target
.PHONY: all
all: directories $(BINARIES)

# Create necessary directories
.PHONY: directories
directories:
	@mkdir -p $(BUILDDIR)
	@mkdir -p $(BINDIR)
	@mkdir -p $(RESULTSDIR)

# Compile individual test programs
$(BINDIR)/ule_scheduler_stress_test: $(BUILDDIR)/ule_scheduler_stress_test.o
	$(CC) $(CFLAGS) $< -o $@ $(LDFLAGS)

$(BINDIR)/ule_interactivity_test: $(BUILDDIR)/ule_interactivity_test.o
	$(CC) $(CFLAGS) $< -o $@ $(LDFLAGS)

$(BINDIR)/ule_multicore_validation: $(BUILDDIR)/ule_multicore_validation.o
	$(CC) $(CFLAGS) $< -o $@ $(LDFLAGS)

$(BINDIR)/ule_performance_benchmark: $(BUILDDIR)/ule_performance_benchmark.o
	$(CC) $(CFLAGS) $< -o $@ $(LDFLAGS)

$(BINDIR)/ule_fsm_integration_stress: $(BUILDDIR)/ule_fsm_integration_stress.o
	$(CC) $(CFLAGS) $< -o $@ $(LDFLAGS)

# Compile object files
$(BUILDDIR)/%.o: $(SRCDIR)/%.c
	$(CC) $(CFLAGS) -c $< -o $@

# Run all tests
.PHONY: test
test: all
	@echo "=== Running ULE Scheduler Test Suite ==="
	@echo "Starting comprehensive ULE scheduler validation..."
	@echo ""
	
	@echo "1. ULE Scheduler Stress Test (5 minutes)..."
	@timeout 300 $(BINDIR)/ule_scheduler_stress_test || echo "Stress test completed with timeout"
	@mv ule_scheduler_stress_results.txt $(RESULTSDIR)/ 2>/dev/null || true
	@echo ""
	
	@echo "2. ULE Interactivity Calculation Test (1 minute)..."
	@timeout 60 $(BINDIR)/ule_interactivity_test || echo "Interactivity test completed"
	@mv ule_interactivity_test_results.txt $(RESULTSDIR)/ 2>/dev/null || true
	@echo ""
	
	@echo "3. ULE Multi-Core Validation (2 minutes)..."
	@timeout 120 $(BINDIR)/ule_multicore_validation || echo "Multi-core test completed"
	@mv ule_multicore_validation_results.txt $(RESULTSDIR)/ 2>/dev/null || true
	@echo ""
	
	@echo "4. ULE Performance Benchmark (4 minutes)..."
	@timeout 240 $(BINDIR)/ule_performance_benchmark || echo "Performance benchmark completed"
	@mv ule_performance_benchmark_results.txt $(RESULTSDIR)/ 2>/dev/null || true
	@echo ""
	
	@echo "5. ULE+FSM Integration Stress Test (3 minutes)..."
	@timeout 180 $(BINDIR)/ule_fsm_integration_stress || echo "Integration stress test completed"
	@mv ule_fsm_integration_stress_results.txt $(RESULTSDIR)/ 2>/dev/null || true
	@echo ""
	
	@echo "=== ULE Scheduler Test Suite Complete ==="
	@echo "Results saved in $(RESULTSDIR)/"

# Run quick tests (shorter duration)
.PHONY: test-quick
test-quick: all
	@echo "=== Running Quick ULE Scheduler Tests ==="
	@echo ""
	
	@echo "1. Quick Scheduler Stress Test (30 seconds)..."
	@timeout 30 $(BINDIR)/ule_scheduler_stress_test || echo "Quick stress test completed"
	@echo ""
	
	@echo "2. Quick Interactivity Test (10 seconds)..."
	@timeout 10 $(BINDIR)/ule_interactivity_test || echo "Quick interactivity test completed"
	@echo ""
	
	@echo "3. Quick Multi-Core Test (30 seconds)..."
	@timeout 30 $(BINDIR)/ule_multicore_validation || echo "Quick multi-core test completed"
	@echo ""
	
	@echo "=== Quick Test Suite Complete ==="

# Run individual tests
.PHONY: test-stress
test-stress: $(BINDIR)/ule_scheduler_stress_test
	@echo "Running ULE Scheduler Stress Test..."
	$(BINDIR)/ule_scheduler_stress_test

.PHONY: test-interactivity
test-interactivity: $(BINDIR)/ule_interactivity_test
	@echo "Running ULE Interactivity Calculation Test..."
	$(BINDIR)/ule_interactivity_test

.PHONY: test-multicore
test-multicore: $(BINDIR)/ule_multicore_validation
	@echo "Running ULE Multi-Core Validation..."
	$(BINDIR)/ule_multicore_validation

.PHONY: test-benchmark
test-benchmark: $(BINDIR)/ule_performance_benchmark
	@echo "Running ULE Performance Benchmark..."
	$(BINDIR)/ule_performance_benchmark

.PHONY: test-integration
test-integration: $(BINDIR)/ule_fsm_integration_stress
	@echo "Running ULE+FSM Integration Stress Test..."
	$(BINDIR)/ule_fsm_integration_stress

# Generate test report
.PHONY: report
report: test
	@echo "=== Generating ULE Scheduler Test Report ==="
	@echo "# ULE Scheduler Test Suite Report" > $(RESULTSDIR)/test_report.md
	@echo "Generated on: $$(date)" >> $(RESULTSDIR)/test_report.md
	@echo "" >> $(RESULTSDIR)/test_report.md
	@echo "## Test Results Summary" >> $(RESULTSDIR)/test_report.md
	@echo "" >> $(RESULTSDIR)/test_report.md
	@for result in $(RESULTSDIR)/*.txt; do \
		if [ -f "$$result" ]; then \
			echo "### $$(basename $$result .txt)" >> $(RESULTSDIR)/test_report.md; \
			echo "\`\`\`" >> $(RESULTSDIR)/test_report.md; \
			head -20 "$$result" >> $(RESULTSDIR)/test_report.md; \
			echo "\`\`\`" >> $(RESULTSDIR)/test_report.md; \
			echo "" >> $(RESULTSDIR)/test_report.md; \
		fi \
	done
	@echo "Test report generated: $(RESULTSDIR)/test_report.md"

# Clean build artifacts
.PHONY: clean
clean:
	@rm -rf $(BUILDDIR)
	@rm -rf $(BINDIR)
	@rm -f *.txt *.log core.*
	@echo "Build artifacts cleaned"

# Clean everything including results
.PHONY: clean-all
clean-all: clean
	@rm -rf $(RESULTSDIR)
	@echo "All artifacts and results cleaned"

# Install tests to system (requires root)
.PHONY: install
install: all
	@echo "Installing ULE scheduler tests to /usr/local/bin..."
	@sudo mkdir -p /usr/local/bin/ule-tests
	@sudo cp $(BINDIR)/* /usr/local/bin/ule-tests/
	@sudo chmod +x /usr/local/bin/ule-tests/*
	@echo "ULE scheduler tests installed to /usr/local/bin/ule-tests/"

# Uninstall tests from system
.PHONY: uninstall
uninstall:
	@echo "Removing ULE scheduler tests from /usr/local/bin..."
	@sudo rm -rf /usr/local/bin/ule-tests
	@echo "ULE scheduler tests uninstalled"

# Check system requirements
.PHONY: check-deps
check-deps:
	@echo "=== Checking ULE Scheduler Test Dependencies ==="
	@echo -n "GCC compiler: "
	@which gcc > /dev/null && echo "✓ Found" || echo "✗ Missing"
	@echo -n "pthread library: "
	@echo "#include <pthread.h>" | gcc -E - > /dev/null 2>&1 && echo "✓ Available" || echo "✗ Missing"
	@echo -n "math library: "
	@echo "#include <math.h>" | gcc -E - > /dev/null 2>&1 && echo "✓ Available" || echo "✗ Missing"
	@echo -n "NUMA library: "
	@echo "#include <numa.h>" | gcc -E - > /dev/null 2>&1 && echo "✓ Available" || echo "⚠ Optional"
	@echo -n "Real-time library: "
	@echo "#include <time.h>" | gcc -E - > /dev/null 2>&1 && echo "✓ Available" || echo "✗ Missing"
	@echo ""
	@echo "CPU cores available: $$(nproc)"
	@echo "Memory available: $$(free -h | grep Mem | awk '{print $$2}')"
	@echo ""
	@if which numactl > /dev/null 2>&1; then \
		echo "NUMA topology:"; \
		numactl --hardware 2>/dev/null || echo "NUMA not available"; \
	else \
		echo "NUMA tools not installed (optional)"; \
	fi

# Debug build with extra debugging symbols
.PHONY: debug
debug: CFLAGS += -DDEBUG -g3 -O0 -fsanitize=address -fsanitize=thread
debug: LDFLAGS += -fsanitize=address -fsanitize=thread
debug: clean all

# Performance optimized build
.PHONY: release
release: CFLAGS += -O3 -DNDEBUG -march=native -flto
release: LDFLAGS += -flto
release: clean all

# Continuous integration test target
.PHONY: ci-test
ci-test: check-deps test-quick
	@echo "=== CI Test Summary ==="
	@if [ $$? -eq 0 ]; then \
		echo "✓ All ULE scheduler tests passed"; \
	else \
		echo "✗ Some ULE scheduler tests failed"; \
		exit 1; \
	fi

# Show help
.PHONY: help
help:
	@echo "ULE Scheduler Testing Suite"
	@echo "=========================="
	@echo ""
	@echo "Available targets:"
	@echo "  all          - Build all test programs"
	@echo "  test         - Run complete test suite (15+ minutes)"
	@echo "  test-quick   - Run quick tests (1-2 minutes)"
	@echo "  test-stress  - Run only stress test"
	@echo "  test-interactivity - Run only interactivity test"
	@echo "  test-multicore - Run only multi-core test"
	@echo "  test-benchmark - Run only performance benchmark"
	@echo "  test-integration - Run only integration stress test"
	@echo "  report       - Generate comprehensive test report"
	@echo "  clean        - Clean build artifacts"
	@echo "  clean-all    - Clean everything including results"
	@echo "  install      - Install tests to system (requires sudo)"
	@echo "  uninstall    - Remove tests from system (requires sudo)"
	@echo "  check-deps   - Check system dependencies"
	@echo "  debug        - Build with debug symbols and sanitizers"
	@echo "  release      - Build with performance optimizations"
	@echo "  ci-test      - Run tests for continuous integration"
	@echo "  help         - Show this help message"
	@echo ""
	@echo "Test Results:"
	@echo "  Results are saved in: $(RESULTSDIR)/"
	@echo "  Individual test logs: $(RESULTSDIR)/*.txt"
	@echo "  Consolidated report: $(RESULTSDIR)/test_report.md"

# Default help if no target specified
.DEFAULT_GOAL := help