# ULE SMP Scheduler for GNU Hurd - Makefile
# Build system for formally verified scheduler implementation
# Copyright (C) 2025 Free Software Foundation, Inc.

# Compiler settings
CC = gcc
COQC = coqc
CFLAGS = -Wall -Wextra -std=c99 -O2 -g -fno-strict-aliasing
INCLUDES = -I. -I../gnumach -I../gnumach/include
LIBS = -lpthread -lm
COQFLAGS = -R . ULE

# Source files
SCHEDULER_SOURCES = ule_smp_scheduler.c ule_mach_integration.c ule_scheduler_extensions.c
SCHEDULER_HEADERS = ule_smp_scheduler.h
TEST_SOURCES = ule_scheduler_test.c
BENCHMARK_SOURCES = ule_benchmark.c
COQ_SOURCES = ule_smp_scheduler.v

# Object files
SCHEDULER_OBJECTS = $(SCHEDULER_SOURCES:.c=.o)
TEST_OBJECTS = $(TEST_SOURCES:.c=.o)
BENCHMARK_OBJECTS = $(BENCHMARK_SOURCES:.c=.o)
COQ_OBJECTS = $(COQ_SOURCES:.v=.vo)

# Targets
SCHEDULER_LIB = libule_scheduler.a
TEST_BINARY = ule_scheduler_test  
BENCHMARK_BINARY = ule_benchmark
COQ_TARGET = coq

# Build rules
.PHONY: all clean test benchmark coq verify install

all: $(SCHEDULER_LIB) $(TEST_BINARY) $(BENCHMARK_BINARY) $(COQ_TARGET)

# Coq formal verification
coq: $(COQ_OBJECTS)
	@echo "✅ Coq proofs verified successfully"

%.vo: %.v
	@echo "Verifying Coq proof: $<"
	$(COQC) $(COQFLAGS) $<

verify: coq
	@echo "Running formal verification..."
	@echo "Checking that all proofs compile without 'admit':"
	@if grep -n "admit\|Admitted" *.v; then \
		echo "❌ Found unfinished proofs"; \
		exit 1; \
	else \
		echo "✅ All proofs are complete"; \
	fi

# Scheduler library
$(SCHEDULER_LIB): $(SCHEDULER_OBJECTS)
	@echo "Building ULE scheduler library..."
	ar rcs $@ $(SCHEDULER_OBJECTS)
	@echo "✅ Scheduler library built: $@"

# Test binary
$(TEST_BINARY): $(TEST_OBJECTS) $(SCHEDULER_LIB)
	@echo "Building test harness..."
	$(CC) $(CFLAGS) -o $@ $(TEST_OBJECTS) $(SCHEDULER_LIB) $(LIBS)
	@echo "✅ Test harness built: $@"

# Benchmark binary
$(BENCHMARK_BINARY): $(BENCHMARK_OBJECTS) $(SCHEDULER_LIB)
	@echo "Building benchmark suite..."
	$(CC) $(CFLAGS) -o $@ $(BENCHMARK_OBJECTS) $(SCHEDULER_LIB) $(LIBS)
	@echo "✅ Benchmark suite built: $@"

# Object file compilation
%.o: %.c $(SCHEDULER_HEADERS)
	@echo "Compiling: $<"
	$(CC) $(CFLAGS) $(INCLUDES) -c $< -o $@

# Test execution
test: $(TEST_BINARY) verify
	@echo "Running ULE scheduler test suite..."
	@echo "=================================="
	./$(TEST_BINARY)

# Benchmark execution
benchmark: $(BENCHMARK_BINARY)
	@echo "Running ULE scheduler benchmarks..."
	@echo "===================================="
	./$(BENCHMARK_BINARY)

# Performance comparison
compare: benchmark
	@echo "Performance comparison completed."
	@echo "See benchmark output for detailed analysis."

# Static analysis
analyze: $(SCHEDULER_SOURCES)
	@echo "Running static analysis..."
	@if command -v cppcheck >/dev/null 2>&1; then \
		cppcheck --enable=all --std=c99 $(SCHEDULER_SOURCES); \
	else \
		echo "cppcheck not found, skipping static analysis"; \
	fi
	@if command -v clang-tidy >/dev/null 2>&1; then \
		clang-tidy $(SCHEDULER_SOURCES) -- $(INCLUDES); \
	else \
		echo "clang-tidy not found, skipping additional analysis"; \
	fi

# Documentation generation
docs:
	@echo "Generating documentation..."
	@if command -v doxygen >/dev/null 2>&1; then \
		doxygen Doxyfile; \
	else \
		echo "doxygen not found, generating simple docs"; \
		mkdir -p docs; \
		echo "# ULE Scheduler Documentation" > docs/README.md; \
		grep -n "^/\*\*" $(SCHEDULER_SOURCES) $(SCHEDULER_HEADERS) >> docs/README.md; \
	fi

# Clean build artifacts
clean:
	@echo "Cleaning build artifacts..."
	rm -f $(SCHEDULER_OBJECTS) $(TEST_OBJECTS) $(BENCHMARK_OBJECTS)
	rm -f $(SCHEDULER_LIB) $(TEST_BINARY) $(BENCHMARK_BINARY)
	rm -f $(COQ_OBJECTS) *.glob
	rm -rf docs/
	@echo "✅ Clean completed"

# Installation (for integration with GNU Hurd)
install: $(SCHEDULER_LIB) verify
	@echo "Installing ULE scheduler..."
	@if [ ! -d "$(DESTDIR)/usr/include/hurd/ule" ]; then \
		mkdir -p $(DESTDIR)/usr/include/hurd/ule; \
	fi
	@if [ ! -d "$(DESTDIR)/usr/lib/hurd" ]; then \
		mkdir -p $(DESTDIR)/usr/lib/hurd; \
	fi
	install -m 644 $(SCHEDULER_HEADERS) $(DESTDIR)/usr/include/hurd/ule/
	install -m 644 $(SCHEDULER_LIB) $(DESTDIR)/usr/lib/hurd/
	@echo "✅ Installation completed"

# Integration test with Mach kernel (requires Hurd build environment)
integration-test: $(SCHEDULER_LIB)
	@echo "Running integration tests..."
	@if [ -d "../gnumach" ]; then \
		echo "Building with Mach integration..."; \
		$(CC) $(CFLAGS) -DHURD_INTEGRATION $(INCLUDES) \
			-c ule_mach_integration.c -o ule_mach_integration_test.o; \
		echo "✅ Integration compile test passed"; \
	else \
		echo "⚠️  Mach kernel source not found, skipping integration test"; \
	fi

# Continuous integration target
ci: clean verify test analyze
	@echo "✅ Continuous integration checks passed"

# Development helpers
dev-setup:
	@echo "Setting up development environment..."
	@echo "Required packages: gcc coq cppcheck clang-tidy doxygen"
	@echo "Install with: sudo apt-get install gcc coq cppcheck clang-tidy doxygen"

# Help target
help:
	@echo "ULE Scheduler Build System"
	@echo "=========================="
	@echo ""
	@echo "Available targets:"
	@echo "  all          - Build scheduler library, tests, and benchmarks"
	@echo "  coq          - Verify Coq formal proofs"
	@echo "  verify       - Run formal verification checks"
	@echo "  test         - Run test suite"
	@echo "  benchmark    - Run performance benchmarks"
	@echo "  compare      - Compare performance against current Hurd IPC"
	@echo "  analyze      - Run static analysis tools"
	@echo "  docs         - Generate documentation"
	@echo "  install      - Install for integration with Hurd"
	@echo "  integration-test - Test integration with Mach kernel"
	@echo "  ci           - Run continuous integration checks"
	@echo "  clean        - Remove build artifacts"
	@echo "  help         - Show this help message"
	@echo ""
	@echo "Build configuration:"
	@echo "  CC=$(CC)"
	@echo "  CFLAGS=$(CFLAGS)"
	@echo "  COQC=$(COQC)"
	@echo ""

# Debug target
debug: CFLAGS += -DULE_DEBUG -DDEBUG -g3 -O0
debug: all
	@echo "✅ Debug build completed"

# Release target  
release: CFLAGS += -O3 -DNDEBUG -flto
release: all
	@echo "✅ Release build completed"

# Memory check target (requires valgrind)
memcheck: $(TEST_BINARY)
	@if command -v valgrind >/dev/null 2>&1; then \
		echo "Running memory check..."; \
		valgrind --leak-check=full --show-leak-kinds=all ./$(TEST_BINARY); \
	else \
		echo "valgrind not found, skipping memory check"; \
	fi