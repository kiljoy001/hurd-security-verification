# Docker Container Deployment Commands

## Save Verification Container for Distribution

### Create Container Image from Current State
```bash
# Commit current verification environment to image
docker commit verification-container hurd-ule-verification:v2.0

# Save container as compressed archive for distribution
docker save hurd-ule-verification:v2.0 | gzip > hurd-verification-container-v2.0.tar.gz
```

### Load Container on Development Systems
```bash
# Load container from archive
gunzip -c hurd-verification-container-v2.0.tar.gz | docker load

# Run interactive verification container
docker run -it --name hurd-verification hurd-ule-verification:v2.0 /bin/bash
```

## Quick Test Execution Commands

### Inside Container Environment
```bash
# Navigate to test directory
cd /home/scott/Repo/hurd-security-verification/scheduler_testing/

# Quick validation (2 minutes)
make test-quick

# Full test suite (15 minutes)
make test

# Individual test components
make ule_scheduler_stress_test && ./ule_scheduler_stress_test
make ule_interactivity_test && ./ule_interactivity_test
make ule_multicore_validation && ./ule_multicore_validation
make ule_fsm_integration_stress && ./ule_fsm_integration_stress
```

### Formal Verification Validation
```bash
# Compile and verify Coq proofs
cd /home/scott/Repo/hurd-security-verification/coq/
coqc complete_verification_standalone.v
coqc proof_code_correspondence.v  
coqc automated_correspondence_checker.v
```

## Container Management

### Start/Stop Container
```bash
# Start container
docker start hurd-verification

# Access running container
docker exec -it hurd-verification /bin/bash

# Stop container
docker stop hurd-verification
```

### Container Resource Monitoring
```bash
# Monitor resource usage
docker stats hurd-verification

# View container logs
docker logs hurd-verification
```

## File Access and Code Export

### Copy Files from Container
```bash
# Copy test results from container
docker cp hurd-verification:/home/scott/Repo/hurd-security-verification/GNU_Hurd_Security_Verification_Report.md ./

# Copy all source code
docker cp hurd-verification:/home/scott/Repo/hurd-security-verification/ ./hurd-verification-src/
```

### Mount Development Directory
```bash
# Run container with mounted local directory
docker run -it -v $(pwd):/workspace hurd-ule-verification:v2.0 /bin/bash
```

## Production Deployment

### Container Specifications
- **Base Image**: Ubuntu 22.04 LTS
- **Memory Requirement**: 8GB+ recommended
- **CPU**: Multi-core support (tested on 16 cores)
- **Storage**: 2GB for container and test data
- **Network**: No special requirements

### CI/CD Integration
```bash
# Pull and test in CI pipeline
docker load < hurd-verification-container-v2.0.tar.gz
docker run --rm hurd-ule-verification:v2.0 /bin/bash -c "cd /home/scott/Repo/hurd-security-verification/scheduler_testing && make test-quick"
```

## Distribution Package

**File**: `hurd-verification-container-v2.0.tar.gz`
**Size**: ~500MB compressed
**Contents**: Complete verification environment with all dependencies
**Checksum**: Generate with `sha256sum hurd-verification-container-v2.0.tar.gz`

This container provides a complete, reproducible environment for GNU Hurd ULE scheduler verification with mathematical guarantees.