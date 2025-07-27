# FSM IPC System Makefile
# Builds and tests the FSM-based IPC implementation

CC = gcc
CFLAGS = -Wall -Wextra -std=c99 -O2 -g
CFLAGS += -D_GNU_SOURCE -D_POSIX_C_SOURCE=200809L
LDFLAGS = -pthread -lm

# Source files
SOURCES = fsm_message.c fsm_routing.c fsm_processor.c fsm_ule_integration.c
HEADERS = fsm_message.h fsm_routing.h fsm_processor.h fsm_ule_integration.h ule_sched_mock.h
OBJECTS = $(SOURCES:.c=.o)

# Test files
TEST_SOURCES = test_fsm_suite.c
TEST_OBJECTS = $(TEST_SOURCES:.c=.o)
SIMPLE_TEST = simple_test
FSM_ULE_TEST = test_fsm_ule_integration

# Targets
LIBRARY = libfsm_ipc.a
TEST_BINARY = test_fsm_suite
BENCHMARK_BINARY = benchmark_fsm

# Default target
all: $(LIBRARY) $(SIMPLE_TEST) $(FSM_ULE_TEST)

# Library target
$(LIBRARY): $(OBJECTS)
	@echo "Creating FSM IPC library..."
	ar rcs $@ $^
	@echo "Library created: $@"

# Test binary
$(TEST_BINARY): $(TEST_OBJECTS) $(LIBRARY)
	@echo "Building test suite..."
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)
	@echo "Test suite built: $@"

# Benchmark binary
$(BENCHMARK_BINARY): benchmark_fsm.o $(LIBRARY)
	@echo "Building benchmark suite..."
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)
	@echo "Benchmark suite built: $@"

# Simple test binary
$(SIMPLE_TEST): simple_test.o $(LIBRARY)
	@echo "Building simple test..."
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)
	@echo "Simple test built: $@"

# FSM+ULE integration test binary
$(FSM_ULE_TEST): test_fsm_ule_integration.o $(LIBRARY)
	@echo "Building FSM+ULE integration test..."
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)
	@echo "FSM+ULE test built: $@"

# Object files
%.o: %.c $(HEADERS)
	@echo "Compiling $<..."
	$(CC) $(CFLAGS) -c $< -o $@

# Run simple test
test: $(SIMPLE_TEST)
	@echo "Running simple FSM IPC test..."
	./$(SIMPLE_TEST)

# Run FSM+ULE integration test
test-ule: $(FSM_ULE_TEST)
	@echo "Running FSM+ULE integration test..."
	./$(FSM_ULE_TEST)

# Run full test suite
test-full: $(TEST_BINARY)
	@echo "Running full FSM IPC test suite..."
	./$(TEST_BINARY)

# Run benchmarks
benchmark: $(BENCHMARK_BINARY)
	@echo "Running FSM IPC benchmarks..."
	./$(BENCHMARK_BINARY)

# Memory check with valgrind
memcheck: $(TEST_BINARY)
	@echo "Running memory leak detection..."
	valgrind --leak-check=full --show-leak-kinds=all --track-origins=yes ./$(TEST_BINARY)

# Performance profiling
profile: $(TEST_BINARY)
	@echo "Running performance profile..."
	perf record -g ./$(TEST_BINARY)
	perf report

# Static analysis
analyze:
	@echo "Running static analysis..."
	cppcheck --enable=all --std=c99 $(SOURCES) $(HEADERS)
	@echo "Running additional checks..."
	clang-tidy $(SOURCES) -- $(CFLAGS)

# Code coverage
coverage: CFLAGS += --coverage
coverage: $(TEST_BINARY)
	@echo "Running code coverage analysis..."
	./$(TEST_BINARY)
	gcov $(SOURCES)
	lcov --capture --directory . --output-file coverage.info
	genhtml coverage.info --output-directory coverage_report
	@echo "Coverage report generated in coverage_report/"

# Debug build
debug: CFLAGS += -DFSM_DEBUG -g3 -O0
debug: clean all

# Release build
release: CFLAGS += -DNDEBUG -O3 -flto
release: clean all

# Documentation
docs:
	@echo "Generating documentation..."
	doxygen Doxyfile

# Install
install: $(LIBRARY)
	@echo "Installing FSM IPC library..."
	cp $(LIBRARY) /usr/local/lib/
	cp $(HEADERS) /usr/local/include/
	ldconfig

# Uninstall
uninstall:
	@echo "Uninstalling FSM IPC library..."
	rm -f /usr/local/lib/$(LIBRARY)
	rm -f /usr/local/include/fsm_*.h

# Clean
clean:
	@echo "Cleaning build artifacts..."
	rm -f $(OBJECTS) $(TEST_OBJECTS) benchmark_fsm.o simple_test.o test_fsm_ule_integration.o
	rm -f $(LIBRARY) $(TEST_BINARY) $(BENCHMARK_BINARY) $(SIMPLE_TEST) $(FSM_ULE_TEST)
	rm -f *.gcov *.gcda *.gcno coverage.info
	rm -rf coverage_report/
	rm -f perf.data*

# Verify formal proofs
verify-proofs:
	@echo "Verifying Coq formal proofs..."
	cd ../coq && coqc fsm_compiled.v && echo "✓ FSM proofs verified"

# Full verification pipeline
verify: all test verify-proofs
	@echo "Full FSM IPC verification complete!"

# Help
help:
	@echo "FSM IPC Build System"
	@echo "Available targets:"
	@echo "  all         - Build library and tests (default)"
	@echo "  test        - Run test suite"
	@echo "  benchmark   - Run performance benchmarks"
	@echo "  memcheck    - Run memory leak detection"
	@echo "  profile     - Run performance profiling"
	@echo "  analyze     - Run static analysis"
	@echo "  coverage    - Generate code coverage report"
	@echo "  debug       - Build debug version"
	@echo "  release     - Build optimized release version"
	@echo "  docs        - Generate documentation"
	@echo "  install     - Install library system-wide"
	@echo "  uninstall   - Remove installed library"
	@echo "  verify      - Full verification (build + test + proofs)"
	@echo "  clean       - Remove build artifacts"
	@echo "  help        - Show this help message"

.PHONY: all test benchmark memcheck profile analyze coverage debug release docs install uninstall clean verify-proofs verify help