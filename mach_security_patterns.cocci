// Coccinelle script to find security-critical patterns in GNU Mach
// AI-Generated Security Analysis by Claude AI  
// Human Operator: Scott J. Guyton
// Focus: Port rights, IPC, reference counting, resource limits

// Pattern 1: Port rights exclusivity violations
// Look for multiple tasks getting receive rights to same port
@@
expression port, task1, task2;
@@
* port->owner_task = task1;
  ...
* port->owner_task = task2;

// Pattern 2: Missing reference count bounds checking
@@
expression port, count;
@@
* port->ref_count = count;

// Pattern 3: Potential reference count overflow
@@
expression port;
@@
* port->ref_count++;

// Pattern 4: Missing resource limit enforcement  
@@
expression task, resource;
@@
* allocate_resource(task, resource);

// Pattern 5: Port cleanup without proper rights checking
@@
expression port;
@@
* kfree(port);

// Pattern 6: IPC message processing without atomicity
@@
expression msg;
@@
* process_message(msg);

// Pattern 7: Memory allocation without zero-initialization check
@@
expression addr, size;
@@
* vm_allocate(..., addr, size, ...);

// Pattern 8: Task creation without proper inheritance setup
@@
expression parent, child;
@@
* task_create(parent, ..., child);

// Pattern 9: Thread creation without task consistency check
@@
expression thread, task;
@@
* thread_create(..., thread);
  ...
* thread->task = task;

// Pattern 10: Port name validation bypass
@@
expression name;
@@
* mach_port_allocate_name(..., name, ...);