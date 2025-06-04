# malloclab: writing a dynamic storage allocator

## Introduction

**IMPORTANT: You will be required to show a demo as part of this assignment. The demo will show 3 parts:**
**1. Design comments at the top of mm.c**
**2. Code comments throughout mm.c**
**3. Demonstrate your heap consistency checker code running**
**See the rubric towards the end of the README for details on signing up for the demo and expectations.**

**IMPORTANT: Read through the ENTIRE document. The heap consistency checker description is meant to help you understand how consistency checking is a critical debugging tool to help you find bugs in your code. The rubric is long, but is meant to help you understand how to write good documentation. There are many hints at the end for how to work on the assignment. The README is long because it is meant to give you a lot of help and guidance with the project, so please take the time to read ALL of it carefully.**

In this lab, you will be writing a dynamic storage allocator for C programs, i.e., your own version of the `malloc`, `free`, and `realloc` functions. You are encouraged to explore the design space creatively and implement an allocator that is correct, space efficient, and fast.

The only file you will be modifying is `mm.c`. *Modifications in other files will not be used in the grading.* You will be implementing the following functions:
- `bool mm_init(void)`
- `void* malloc(size_t size)`
- `void free(void* ptr)`
- `void* realloc(void* oldptr, size_t size)`
- `bool mm_checkheap(int line_number)`

You are encouraged to define other (static) helper functions, structures, etc. to better structure your code.

## Description of the dynamic memory allocator functions

- `mm_init`: Before calling `malloc`, `realloc`, `calloc`, or `free`, the application program (i.e., the trace-driven driver program that will evaluate your code) calls your `mm_init` function to perform any necessary initializations, such as allocating the initial heap area. You should NOT call this function. Our code will call this function before the other functions so that this gives you an opportunity to initialize your implementation. The return value should be true on success and false if there were any problems in performing the initialization.

- `malloc`: The `malloc` function returns a pointer to an allocated block payload of at least `size` bytes. The entire allocated block should lie within the heap region and should not overlap with any other allocated chunk. If you are out of space and `mm_sbrk` is unable to extend the heap, then you should return NULL. Similar to how the standard C library (libc) always returns payload pointers that are aligned to 16 bytes, your malloc implementation should do likewise and always return 16-byte aligned pointers.

- `free`: The `free` function frees the block pointed to by `ptr`. It returns nothing. This function is only guaranteed to work when the passed pointer (`ptr`) was returned by an earlier call to `malloc`, `calloc`, or `realloc` and has not yet been freed. If `ptr` is NULL, then `free` should do nothing.

- `realloc`: The `realloc` function returns a pointer to an allocated region of at least `size` bytes with the following constraints.

    - if `ptr` is NULL, the call is equivalent to `malloc(size)`

    - if `size` is equal to zero, the call is equivalent to `free(ptr)` and NULL is returned

    - if `ptr` is not NULL, it must have been returned by an earlier call to `malloc`, `calloc`, or `realloc`. The call to `realloc` changes the size of the memory block pointed to by `ptr` (the *old block*) to `size` bytes and returns the address of the new block. Notice that the address of the new block might be the same as the old block, or it might be different, depending on your implementation, the amount of internal fragmentation in the old block, and the size of the `realloc` request.
    The contents of the new block are the same as those of the old `ptr` block, up to the minimum of the old and new sizes. Everything else is uninitialized. For example, if the old block is 8 bytes and the new block is 12 bytes, then the first 8 bytes of the new block are identical to the first 8 bytes of the old block and the last 4 bytes are uninitialized. Similarly, if the old block is 8 bytes and the new block is 4 bytes, then the contents of the new block are identical to the first 4 bytes of the old block.

These semantics match the the semantics of the corresponding libc `malloc`, `realloc`, and `free` functions. Run `man malloc` to view complete documentation.

## Heap consistency checker

Dynamic memory allocators are notoriously tricky beasts to program correctly and efficiently. They are difficult to program correctly because they involve a lot of untyped pointer manipulation and low-level manipulation of bits and bytes. You will find it very helpful to write a heap checker `mm_checkheap` that scans the heap and checks it for consistency. The heap checker will check for *invariants* which should always be true.

Some examples of what a heap checker might check are:
- Is every block in the free list marked as free?
- Are there any contiguous free blocks that somehow escaped coalescing?
- Is every free block actually in the free list?
- Do the pointers in the free list point to valid free blocks?
- Do any allocated blocks overlap?
- Do the pointers in a heap block point to valid heap addresses?

You should implement checks for any invariants you consider prudent. It returns true if your heap is in a valid, consistent state and false otherwise. You are not limited to the listed suggestions nor are you required to check all of them. You are encouraged to print out error messages when the check fails. You can use `dbg_printf` to print messages in your code in debug mode. To enable debug mode, uncomment the line `#define DEBUG`.

To call the heap checker, you can use `mm_checkheap(__LINE__)`, which will pass in the line number of the caller. This can be used to identify which line detected a problem.

## Support routines

The `memlib.c` package simulates the memory system for your dynamic memory allocator. You can invoke the following functions in `memlib.c`:

- `void* mm_sbrk(int incr)`: Expands the heap by `incr` bytes, where `incr` is a positive non-zero integer. It returns a generic pointer to the first byte of the newly allocated heap area. The semantics are identical to the Unix `sbrk` function, except that `mm_sbrk` accepts only a non-negative integer argument. You must use our version, `mm_sbrk`, for the tests to work. Do NOT use `sbrk`.

- `void* mm_heap_lo(void)`: Returns a generic pointer to the first byte in the heap.

- `void* mm_heap_hi(void)`: Returns a generic pointer to the last byte in the heap.

- `size_t mm_heapsize(void)`: Returns the current size of the heap in bytes.

- `size_t mm_pagesize(void)`: Returns the system's page size in bytes (4K on Linux systems).

- `void* memset(void* ptr, int value, size_t n)`: Sets the first n bytes of memory pointed to by ptr to value.

- `void* memcpy(void* dst, const void* src, size_t n)`: Copies n bytes from src to dst.

Not all of these functions will be needed (only mm_sbrk is truly necessary), but they are provided in case you would like to use them.

## Programming Rules

- You are not allowed to change any of the interfaces in `mm.c`.

- You are not allowed to invoke any memory-management related library calls or system calls. For example, you are not allowed to use `sbrk`, `brk`, or the standard library versions of `malloc`, `calloc`, `free`, or `realloc`. Instead of `sbrk`, you should use our provided `mm_sbrk`.

- Your code is expected to work in 64-bit environments, and you should assume that allocation sizes and offsets will require 8 byte (64-bit) representations.

- You are not allowed to use macros as they can be error-prone. The better style is to use static functions and let the compiler inline the simple static functions for you.

- You are limited to 128 bytes of global space for arrays, structs, etc. If you need large amounts of space for storing extra tracking data, you can put it in the heap area.

## Evaluation and testing your code

You will receive zero points if:
- You violate the academic integrity policy (sanctions can be greater than just a 0 for the assignment)
- You don't show your partial work by periodically adding, committing, and pushing your code to GitHub
- You break any of the programming rules
- Your code does not compile/build
- Your code crashes the grading script

Otherwise, your grade will be calculated as follows:
- [100 pts] Checkpoint 1: This part of the assignment tests the correctness of your code and that your code correctly reuses memory. Most of the points are based on the number of trace files that succeed (3 points per trace file). The remaining points are for (i) passing all the trace files and (ii) meeting a minimum space utilization to ensure the code is correctly reusing memory. Having a space utilization below this threshold indicates your code likely has a bug where space is not reused and you may be extending the heap for most malloc calls. Throughput will not be tested in this checkpoint.

- [100 pts] Checkpoint 2: This part of the assignment requires that your code is entirely functional and tests the space utilization (60%) and throughput (40%) of your code. Each metric will have a min and max target (i.e., goal) where if your utilization/throughput is above the max, you get full score and if it is below the min, you get no points. Partial points are assigned proportionally between the min and max. Additionally, there is a required minimum utilization and throughput where you will get a 0 for the entire checkpoint if either metric is below the required minimum. The performance goals in checkpoint 2 are significantly reduced compared to the final submission.

    - Space utilization (60%): The space utilization is calculated based on the peak ratio between the aggregate amount of memory used by the testing tool (i.e., allocated via `malloc` or `realloc` but not yet freed via `free`) and the size of the heap used by your allocator. You should design good policies to minimize fragmentation in order to increase this ratio.

    - Throughput (40%): The throughput is a performance metric that measures the average number of operations completed per second. **As the performance of your code can vary between executions and between machines, your score as you're testing your code is not guaranteed and is meant to give you a general sense of your performance.**

    There will be a balance between space efficiency and speed (throughput), so you should not go to extremes to optimize either the space utilization or the throughput only. To receive a good score, you must achieve a balance between utilization and throughput.

- [100 pts] Final submission: This part of the assignment is graded similarly to Checkpoint 2, except that the grading curve has not been significantly reduced as is the case with Checkpoint 2. 

To test your code, first compile/build your code by running: `make`. You need to do this every time you change your code for the tests to utilize your latest changes.

To run all the tests *after* building your code, run: `make test`.

To test a single trace file *after* building your code, run: `./mdriver -f traces/tracefile.rep`.

Each trace file contains a sequence of allocate, reallocate, and free commands that instruct the driver to call your `malloc`, `realloc`, and `free` functions in some sequence.

Other command line options can be found by running: `./mdriver -h`

To debug your code with gdb, run: `gdb mdriver`.

## Handin

Similar to the last assignment, we will be using GitHub for managing submissions, and **you must show your partial work by periodically adding, committing, and pushing your code to GitHub**. This helps us see your code if you ask any questions on Canvas (please include your GitHub username) and also helps deter academic integrity violations.

Additionally, please input the desired commit number that you would like us to grade in Canvas. You can get the commit number from github.com. In your repository, click on the commits link to the right above your files. Find the commit from the appropriate day/time that you want graded. Click on the clipboard icon to copy the commit number. Note that this is a much longer number than the displayed number. Paste your very long commit number and only your commit number in this assignment submission textbox.

## Hints

- *Refer to the lectures for an overview of a recommended malloc design.* While you are not required to use the design, our suggestions give you a good starting point. We recommend starting with an implicit free list design (i.e., headers and footers with splitting and coalescing) for checkpoint 1 so that you have a baseline version that works. If this is working correctly, it'll likely be very slow (taking half an hour to hours depending on your machine). See the later hints for debugging tips. For checkpoint 2, you should then build on top of the implicit free list design to embed a linked list within the free block space. This is known as an explicit free list design, and it should improve throughput and possibly utilization. The linked list is embedded within the free block space and allows a quick way to find all the free blocks in the heap. At this point, we recommend going from 1 linked list to multiple linked lists for the free blocks, where each linked list represents a range of sizes for the free blocks in the list. This is known as a segregated free list design and will drastically improve the throughput, with the code taking seconds to a few minutes to run the tests. For the final submission, we recommend trying the footer optimization as described in lecture, which can improve help space utilization by a decent amount. All of these optimizations build on top of each other, so it's a good way to gradually increase the complexity and performance of the code. Do NOT attempt to implement all the optimizations right away since the debugging will be too difficult. It is far easier to debug one optimization at a time, and development will be a lot easier from gradually increasing the complexity through these optimizations. 

- *Use the `mdriver` `-c` option for correctness testing.* You can use the -c flag with a trace file to just test the correctness of a single trace file. This will speed up the initial debugging since it will be much faster to test a single trace. You should start testing the tiny trace files ending in `-short.rep` and look at the memory in gdb via the x command. In particular, the `syn-example-short.rep` trace file matches the malloc practice quiz, so stepping through the code in gdb and viewing the memory via the gdb x command will allow you to compare against the quiz. Note that the testing will run each trace multiple times to check for initialization bugs, so as you're debugging, you may hit breakpoints that look like the trace is restarting, and this is expected behavior.

- *Use gdb; watchpoints can help with finding corruption.* `gdb` will help you isolate and identify out of bounds memory references as well as where in the code the SEGFAULT occurs. To assist the debugger, you may want to compile with `make debug` to produce unoptimized code that is easier to debug. To revert to optimized code, run `make release` for improved performance. Additionally, using watchpoints in gdb can help detect where corruption is occurring if you know the address that is being corrupted.

- *Encapsulate your pointer arithmetic and bit manipulation in static helper functions.* Pointer arithmetic in your implementation can be confusing and error-prone because of all the casting that is necessary. You can reduce the complexity significantly by writing static helper functions for your pointer operations and bit manipulation. The compiler should inline these simple functions for you.

- *Use clear names for indicating what a pointer points to.* There is a difference between whether a pointer points to the beginning of a block or if it points to the beginning of the user payload space. Using good variable/parameter names will help avoid misinterpreting what a pointer points to.

- *Write a good heap checker.* This will help detect errors much closer to when they occur. This is one of the most useful techniques for debugging data structures like the malloc memory structure.

- *Design your code in modules that can be used as building blocks.* Malloc is fundamentally just a complex data structure built up of multiple data structures. You should design your code to be modular by separating out sets of related functions that perform a specific task. For example, you could isolate all linked list code and have a set of functions that simply manage a linked list. You can then embed the linked list in the memory blocks and call these functions to help insert/remove without having all the insertion/removal logic mixed together with all the malloc logic. That way, any code that splits and coalesces blocks can just reuse your common linked list code without worrying about whether there's a linked list bug, and your linked list code would not need to worry about how it is used.

- *Use git to track your different versions.* `git` will allow you to track your code changes to help you remember what you've done in the past. It can also provide an easy way to revert to prior versions if you made a mistake.

- *Use the `mdriver` `-v` and `-V` options.* These options allow extra debug information to be printed.
