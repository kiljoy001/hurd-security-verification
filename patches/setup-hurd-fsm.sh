#!/bin/bash
# GNU Hurd FSM IPC Cross-Compilation Setup Script
# This script sets up a complete Hurd development environment with FSM IPC patches

set -e  # Exit on any error

echo "=== GNU Hurd FSM IPC Development Environment Setup ==="

# Update package lists
echo "Updating package lists..."
apt update

# Install essential build tools
echo "Installing build dependencies..."
apt install -y build-essential git autoconf automake libtool pkg-config \
               flex bison texinfo gawk wget curl rsync

# Install Hurd-specific dependencies
echo "Installing Hurd development dependencies..."
apt install -y mig libparted-dev uuid-dev zlib1g-dev libblkid-dev \
               libncurses5-dev libreadline-dev

# Install cross-compilation toolchain
echo "Installing cross-compilation toolchain..."
apt install -y gcc-i686-gnu binutils-i686-gnu

# Install QEMU and boot tools for testing
echo "Installing virtualization and boot tools..."
apt install -y qemu-system-i386 genisoimage grub-pc-bin xorriso

# Set up environment variables
export TARGET=i686-gnu
export PREFIX=/usr/local/cross-hurd
export PATH="$PREFIX/bin:$PATH"

echo "Environment variables set:"
echo "  TARGET=$TARGET"
echo "  PREFIX=$PREFIX"

# Create development directory structure
echo "Setting up development directories..."
mkdir -p /workspace/hurd-dev
cd /workspace/hurd-dev

# Clone GNU Mach (microkernel)
echo "Cloning GNU Mach..."
if [ ! -d "gnumach" ]; then
    git clone https://git.savannah.gnu.org/git/gnumach.git
    cd gnumach
    git checkout master
    cd ..
else
    echo "GNU Mach already cloned"
fi

# Clone GNU Hurd (servers and libraries)
echo "Cloning GNU Hurd..."
if [ ! -d "hurd" ]; then
    git clone https://git.savannah.gnu.org/git/hurd/hurd.git
    cd hurd
    git checkout master
    cd ..
else
    echo "GNU Hurd already cloned"
fi

# Clone MiG (Mach Interface Generator)
echo "Cloning MiG..."
if [ ! -d "mig" ]; then
    git clone https://git.savannah.gnu.org/git/mig.git
    cd mig
    git checkout master
    cd ..
else
    echo "MiG already cloned"
fi

# Build MiG first (required for Hurd)
echo "Building MiG..."
cd /workspace/hurd-dev/mig
if [ ! -f "Makefile" ]; then
    autoreconf -fiv
    ./configure --target=i686-gnu --prefix=$PREFIX
fi
make -j$(nproc)
make install
cd ..

echo "MiG installation complete"

# Apply FSM IPC patches to GNU Mach
echo "Applying FSM IPC patches to GNU Mach..."
cd /workspace/hurd-dev/gnumach

# Create FSM IPC directory structure in GNU Mach
mkdir -p fsm_ipc
mkdir -p include/fsm_ipc

# Copy FSM IPC source files to GNU Mach
echo "Copying FSM IPC implementation files..."
cp /workspace/fsm_ipc/fsm_message.c fsm_ipc/
cp /workspace/fsm_ipc/fsm_message.h include/fsm_ipc/
cp /workspace/fsm_ipc/fsm_routing.c fsm_ipc/
cp /workspace/fsm_ipc/fsm_routing.h include/fsm_ipc/
cp /workspace/fsm_ipc/fsm_processor.c fsm_ipc/
cp /workspace/fsm_ipc/fsm_processor.h include/fsm_ipc/
cp /workspace/fsm_ipc/fsm_ule_integration.c fsm_ipc/
cp /workspace/fsm_ipc/fsm_ule_integration.h include/fsm_ipc/
cp /workspace/fsm_ipc/ule_sched_mock.h include/fsm_ipc/

# Copy kernel syscall implementation
cp /workspace/patches/gnumach-fsm-syscalls.c fsm_ipc/fsm_syscalls.c

# Create FSM syscalls header
cat > include/fsm_ipc/fsm_syscalls.h << 'EOF'
/* FSM IPC System Call Declarations for GNU Mach
 * Copyright (C) 2025 Free Software Foundation, Inc.
 */

#ifndef _FSM_IPC_SYSCALLS_H_
#define _FSM_IPC_SYSCALLS_H_

#include <mach/kern_return.h>
#include <mach/port.h>
#include <mach/message.h>

/* FSM IPC system call prototypes */
extern kern_return_t fsm_msg_send_trap(
    mach_port_name_t dest_port,
    vm_address_t msg_addr,
    mach_msg_size_t msg_size,
    mach_msg_timeout_t timeout);

extern kern_return_t fsm_msg_receive_trap(
    mach_port_name_t source_port,
    vm_address_t msg_addr,
    mach_msg_size_t max_size,
    mach_msg_timeout_t timeout);

extern kern_return_t fsm_get_performance_stats(
    vm_address_t stats_addr,
    mach_msg_size_t stats_size);

/* Initialization and shutdown */
extern kern_return_t fsm_ipc_init(void);
extern void fsm_ipc_shutdown(void);

#endif /* _FSM_IPC_SYSCALLS_H_ */
EOF

# Apply main patch to GNU Mach build system
echo "Applying build system patches..."

# Patch Makefile.am to include FSM IPC sources
if ! grep -q "fsm_ipc/fsm_message.c" Makefile.am; then
    cat >> Makefile.am << 'EOF'

# FSM IPC subsystem
libkernel_a_SOURCES += \
	fsm_ipc/fsm_message.c \
	fsm_ipc/fsm_routing.c \
	fsm_ipc/fsm_processor.c \
	fsm_ipc/fsm_ule_integration.c \
	fsm_ipc/fsm_syscalls.c
EOF
fi

# Add FSM syscalls to syscall table
if ! grep -q "fsm_msg_send_trap" kern/syscall_sw.c; then
    echo "Patching syscall table..."
    # Add FSM includes
    sed -i '/^#include <ipc\/ipc_kmsg.h>/a #include <fsm_ipc/fsm_syscalls.h>' kern/syscall_sw.c
    
    # Add FSM syscalls to trap table (find a good insertion point)
    sed -i '/kern_invalid.*89/a \\t/* FSM IPC syscalls */\n\t{\tfsm_msg_send_trap, 4, 4,\n\t\t"fsm_msg_send" },\t\t\t/* 90 */\n\t{\tfsm_msg_receive_trap, 4, 4,\n\t\t"fsm_msg_receive" },\t\t\t/* 91 */' kern/syscall_sw.c
fi

# Add FSM syscalls to mach_traps.h
if ! grep -q "fsm_msg_send_trap" include/mach/mach_traps.h; then
    cat >> include/mach/mach_traps.h << 'EOF'

/* FSM IPC system calls */
extern kern_return_t fsm_msg_send_trap(
	mach_port_name_t dest_port,
	vm_address_t msg_addr,
	mach_msg_size_t msg_size,
	mach_msg_timeout_t timeout);

extern kern_return_t fsm_msg_receive_trap(
	mach_port_name_t source_port,
	vm_address_t msg_addr,
	mach_msg_size_t max_size,
	mach_msg_timeout_t timeout);
EOF
fi

# Configure GNU Mach with FSM IPC support
echo "Configuring GNU Mach with FSM IPC..."
if [ ! -f "Makefile" ]; then
    autoreconf -fiv
    ./configure --target=i686-gnu --prefix=$PREFIX \
                --enable-fsm-ipc \
                --enable-device-drivers=ide,net,pcmcia,wireless \
                --host=i686-gnu
fi

# Build GNU Mach with FSM IPC
echo "Building GNU Mach with FSM IPC support..."
make -j$(nproc)

if [ $? -eq 0 ]; then
    echo "✓ GNU Mach with FSM IPC built successfully!"
    echo "  Kernel: $(pwd)/gnumach"
    ls -la gnumach
else
    echo "✗ GNU Mach build failed"
    exit 1
fi

cd /workspace

echo "=== FSM IPC Kernel Build Complete ==="
echo ""
echo "Next steps:"
echo "1. Create test programs to measure real kernel IPC performance"
echo "2. Boot the patched kernel in QEMU"
echo "3. Compare real kernel IPC vs userspace simulation performance"
echo ""
echo "Kernel location: /workspace/hurd-dev/gnumach/gnumach"
echo "FSM IPC sources: /workspace/hurd-dev/gnumach/fsm_ipc/"