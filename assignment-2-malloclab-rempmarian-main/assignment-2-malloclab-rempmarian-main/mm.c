/*
 * mm.c
 *
 * Name: Marian Rempola
 *
 * [Structure] For this dynamic memory allocator, I'm using a Segregated Free List of chunks that I can keep track of when I'm 
 * allocating, freeing, reallocating, etc. The helper functions are to support this structure. To optimize heap space, I am splitting
 * the bigger chunks and also coalescing whenever I free() chunks (as professor advised). To improve utilization, I am optimizing my 
 * footer, so that it will only store them when needed (see below for more information on how I am doing that).
 * 
 *  1. Improving Throughput (segregtaed free list): multiple free lists to handle chunks of different sizes 
 * --> reduces search time for free chunk because it will only search depending on the size 
 * 
 *  2. Improve utilization (ftr optimization): ftr used only for coalesciing
 * ftr is only used for size of a free chunk IF the previous chunk is free
 * hdr = 10000, first bit is if alloc or not; next bit is for previous chunk's alloc, next 2 is free
 * (look at pic from OH)
 * --> coalesce(): when coalescing chunk with a free prev chunk, ftr of the prev chunk should be the new (merged) chunk size
 *                  if prev chunk is allocated, can't rely on ftr (user hdr instead)
 * --> update the helper and accessor functions to support footer optimization
 * 
 * Citations: Professor's slides and code examples, (a lot of) Office Hours help, HW 1 Doubly Linked List problem, and Chapter 9 in the book
 */
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <stdint.h>
#include <stdbool.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
//#define DEBUG

#ifdef DEBUG
// When debugging is enabled, the underlying functions get called
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
// When debugging is disabled, no code gets generated
#define dbg_printf(...)
#define dbg_assert(...)
#endif  // DEBUG

// do not change the following!
#ifdef DRIVER
// create aliases for driver tests
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mm_memset
#define memcpy mm_memcpy
#endif // DRIVER

#define ALIGNMENT 16

// rounds up to the nearest multiple of ALIGNMENT
static size_t align(size_t x)
{
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

/*----------------------------------------------------------------------------------*/
// definining my STATIC INLINE FUNCTIONS and variables to make accessing data easier

static inline size_t ptrSize(void *ptr) {
    // getting size of ptr by deferrencing ptr and bitmasking 
    return *(size_t *)(ptr) & ~0x3;
}

static inline int allocatedBit(void *ptr) {
    // getting the allocated bit stored in the meta data to see if the ptr is allocated or not
    return *(size_t *)(ptr) & 0x1;
}

// helper function to get previous chunk's allocated bit
static inline int prevAllocatedBit(void *ptr) {
    return *(size_t *)(ptr) & 0x2;
}

static inline void *hdr(void *ptr) {
    // access hdr by moving back 8 bytes from the chunk ptr
    return ((char *)(ptr) - 8);
}

static inline void *ftr(void *ptr) {
    // access ftr by going to the chunk and moving back 16 (hdr + ftr size)
    return ((char *)(ptr) + ptrSize(hdr(ptr)) - 16);
}

// helper functions to get next chunk and previous chunk given ptr
static void *nextChunk(void *ptr ) {
    return (char*)(ptr) + ptrSize((char*)(ptr) - 8);
}

static void *prevChunk(void *ptr) {
    return (char*)(ptr) - ptrSize((char*)(ptr) - 16);
}

// helper function to get proper free list position
static inline int getFlIndex(size_t size) {
    if (size <= 32) return 0;
    else if (size <= 64) return 1;
    else if (size <= 128) return 2;
    else if (size <= 256) return 3;
    else if (size <= 512) return 4;
    else if (size <= 1024) return 5;
    else if (size <= 2048) return 6;
    else if (size <= 4096) return 7;
    else if (size <= 8192) return 8;
    else return 9; // if size > 8192
}

// defining a free list structure named 'FreeList' to keep track of the free space
typedef struct FreeList{
    // ptrs to the next and previous chunks
    struct FreeList *prev; 
    struct FreeList *next;
} FreeList;

void *heapStart; // points to first byte in heap

// defining my array of FreeLists (segregated FreeList) 
FreeList *fl0;
FreeList *fl1;
FreeList *fl2;
FreeList *fl3;
FreeList *fl4;
FreeList *fl5;
FreeList *fl6;
FreeList *fl7;
FreeList *fl8;
FreeList *fl9;

// struct FreeList segregatedFL[6]; //using 6 free lists since that's the most I have space for

// declaring my static helper functions: explanation is above each function definition 
static FreeList* getFl(int i);
static void *firstFit(size_t size); 
static void put(void *chunk, size_t properSize);
static void removeChunk(FreeList *ptr);
static void addChunk(FreeList *newChunk, FreeList *fl);
static void *coalesce(void *ptr);
static void *extendHeap(size_t properSize);

/*----------------------------------------------------------------------------------*/
/*
 * mm_init: returns false on error, true on success.
 * Overview: allocate initial heap area 
 * Notes: don't call this function
 */
bool mm_init(void)
{
    // allocate initial heap area: metadata and 6 free lists
    heapStart = mm_sbrk(32 + (10*16));
    // if asking for memory didn't work, then return error message
    if (heapStart == (void *)-1) {
        perror("Failed to initialize heap\n");
        return false;
    }
    
    // set metadata based on the image provided in the pdf
    // set prologue: 8 bytes
    *(size_t *) heapStart = 0; 
    // set header: 16 bytes
    *(size_t *) (heapStart + (21*8)) = (16 | 1);
    // set footer: 16 bytes
    *(size_t *) (heapStart + (22*8)) = (16 | 1); 
    // set epilogue: set to 11 (need to use epilogue in extendHeap())
    *(size_t *) (heapStart + (23*8)) = (0 | 1); 

    // Initializing segregated free lists (pointing it to correct posn)
    fl0 = (heapStart + 8);
    fl1 = (heapStart + 24);
    fl2 = (heapStart + 40);
    fl3 = (heapStart + 56);
    fl4 = (heapStart + 72);
    fl5 = (heapStart + 88);
    fl6 = (heapStart + 104);
    fl7 = (heapStart + 120);
    fl8 = (heapStart + 136);
    fl9 = (heapStart + 152);

    // Initialize each free list as an empty circular doubly linked list
    fl0->prev = fl0;
    fl0->next = fl0;
    fl1->prev = fl1;
    fl1->next = fl1;
    fl2->prev = fl2;
    fl2->next = fl2;
    fl3->prev = fl3;
    fl3->next = fl3;
    fl4->prev = fl4;
    fl4->next = fl4;
    fl5->prev = fl5;
    fl5->next = fl5;
    fl6->prev = fl6;
    fl6->next = fl6;
    fl7->prev = fl7;
    fl7->next = fl7;
    fl8->prev = fl8;
    fl8->next = fl8;
    fl9->prev = fl9;
    fl9->next = fl9;

    // move start of the heap ptr at the ftr of the prologue
    heapStart += 22*8;
    // need to extend heap to 4096 bytes for free lists since I'm not using a dummy anymore
    void *ptr = extendHeap(4096);

    if(ptr==NULL) {
        return false;
    }
    return true;
}

/* Helper function to update the next chunk's bit whenever I free/alloc a chunk*/
void updateNext(void *ptr) {
    if(nextChunk(ptr) != NULL) {
        // determining what to set the nextChunk to
        size_t alloc;
        size_t nextAlloc = allocatedBit(hdr(nextChunk(ptr)));
        size_t thisAlloc = allocatedBit(hdr(ptr));

        if (nextAlloc && thisAlloc) { alloc = 3;} //0011
        else if (!nextAlloc && thisAlloc) { alloc = 2;} //0010
        else if (nextAlloc && !thisAlloc) { alloc = 1;} //0001
        else { alloc = 0;} //0000
        
        // update next chunk's previous allocation bit
        void *next = nextChunk(ptr);
        size_t nextSize = ptrSize(hdr(next));
        *(size_t *) hdr(next) = nextSize | alloc;
    }
}

/*----------------------------------------------------------------------------------*/
/*
 * malloc: returns a ptr to allocated block payload of at least 'size' bytes
 * Overview: 1. allocated memory block shall be within heap and not overlap with allocated memory;
 *           2. call mm_sbrk() if we don't have enough space
 *           3. return NULL and print error statement if both conditions above fail
 */
void* malloc(size_t size)
{
    // check if 'size' requested is valid
    if(size == 0) {
        return NULL;
    }

    // properSize is the corrected value of 'size
    size_t properSize;
    // setting proper size to ask memory for: mininmum of 32 bytes but don't need 32 if the user data is small enuogh 
    if (size <= 16) {
        properSize = 32; 
    } else {
        properSize = align(size + 32);
    }  

    // [1. Look for a free chunk of 'size' bytes in the proper free list]
    // helper function 'firstFit': see where in heap to place (using best-fit approach)
    char *chunk = firstFit(properSize); 
    // check if heap was able to find a chunk of properSize in the correct free list
    if(chunk != NULL) {
        // helper function 'put': put the chunk in heap with properSize
        put(chunk, properSize);
        // update previousAlloc --> i.e. update next block's hdr to 1 (allocated)
        updateNext(chunk);
        return chunk;
    }

    // [2. If it doesn't fit in heap, ask OS for more memory using mm_sbrk()] 
    // helper function 'extendHeap': ask OS for right amount of memory and will return the new chunk to allocate memory at
    // passing this chunk's alloc bit
    chunk = extendHeap(properSize);
    // check if extending heap failed
    if(chunk == NULL) {
        perror("Extending heap failed\n");
        return NULL;
    }

    // else put the new chunk in heap
    put(chunk, properSize);
    // update prevAllocated bit --> i.e. update next block's hdr to 1 (allocated)
    updateNext(chunk);
    return chunk;
}

/* Helper function to get correct free list based on the index passed*/
static FreeList* getFl(int i) {
    if (i == 0) {return fl0;}
    else if (i == 1) {return fl1;}
    else if (i == 2) {return fl2;}
    else if (i == 3) {return fl3;}
    else if (i == 4) {return fl4;}
    else if (i == 5) {return fl5;}
    else if (i == 6) {return fl6;}
    else if (i == 7) {return fl7;}
    else if (i == 8) {return fl8;}
    else {return fl9;}
}

/* Helper Function to find the first fit of 'size' bytes in heap of the FreeList.
    Appropriate free list to add 'size' bytes to will depend on the size requested.
   returns ptr to heap for first fit chunk in the appropriate free list
*/
static void *firstFit(size_t size){
    // ptrs to the best fit chunk in the appropriate free list
    FreeList *ptr;
    FreeList *fl = getFl(getFlIndex(size));

    // finding place to put the chunk in, starting from the appropriate free list
    for(int i =  getFlIndex(size); i < 10; i++) {
        fl = getFl(i);
        // go through the specific free list
        for(ptr = fl->next; ptr != fl; ptr = ptr->next) {
            // if appropriate chunk of at least size is found, return that chunk
            if(size <= ptrSize(hdr(ptr))) {
                return ptr;
            }
        }
    }

    // no chunk found
    return NULL;
}

/* Helper Function to extend the heap by asking for the correct amount and update the free list
    returns the chunk to allocate at */
static void* extendHeap(size_t properSize) {
    size_t alignedSize = align(properSize);

    // ask OS for memory of size the closest aligned amount of properSize
    char* chunk = mem_sbrk(alignedSize);
    // check if asking for memory worked
    if(chunk == (void*)-1) {
        perror("Extending heap failed\n");
        return NULL;
    }

    // check if this is the first chunk being placed in the heap (aka if it's b/w pro and epilogue)
    if ((allocatedBit(hdr(prevChunk(chunk))) == 1 && ptrSize(hdr(prevChunk(chunk))) == 16) 
        && ptrSize(hdr(nextChunk(chunk))) == 0) {
        *(size_t*)hdr(chunk) = alignedSize | 2; // 0010
        *(size_t*)ftr(chunk) = alignedSize | 2;
    } else {
        *(size_t*)hdr(chunk) = alignedSize | 0;
        *(size_t*)ftr(chunk) = alignedSize | 0;
    }

    // point to the next chunk and create new epilogue
    *(size_t*)hdr(nextChunk(chunk)) = 0 | 1; // size 0, and allocated bit = 1

    return coalesce(chunk);
}

/* Helper Function to put the 'properSize' bytes into heap at 'chunk' */
static void put(void *chunk, size_t properSize) {
    if(chunk == NULL) {
        perror("Invalid ptr passed in put()");
        return;
    }
  
    // size of the chunk
    size_t chunkSize = ptrSize(hdr(chunk));
    // ptr to correct free list
    FreeList *fl = getFl(getFlIndex(chunkSize));
    
    // [1. if chunk is too big for properSize, we can split to save memory!]
    if ((chunkSize - properSize) >= 32) { // Only split if the remaining chunk is large enough
        // remove chunk from free list
        removeChunk(chunk);
        // update hdr and ftr to mark chunk as allocated, set allocated bit (bit 0)
        *(size_t *)hdr(chunk) = properSize | 1;
        *(size_t *)ftr(chunk) = properSize | 1;
        // update prevAllocated bit
        updateNext(prevChunk(chunk));

        // place the next chunk in heap
        chunk = nextChunk(chunk);
        // update hdr and ftr size and alloc
        *(size_t *)hdr(chunk) = (chunkSize - properSize) | 0;
        *(size_t *)ftr(chunk) = (chunkSize - properSize) | 0; 
        // place (chunkSize - properSize) to the free list
        fl = getFl(getFlIndex(chunkSize - properSize));
        addChunk(chunk, fl);
    }
    // [2. if the properSize fits appropriately]
    else {
         // remove chunk from the free list
        removeChunk(chunk);
        // update hdr and ftr to alloc
        *(size_t *)hdr(chunk) = chunkSize | 1;
        // *(size_t *)ftr(chunk) = chunkSize | 1;
        // update prevAllocated bit
        updateNext(prevChunk(chunk));
    }
}

/* Helper Function to remove the chunk from the appropriate free list*/
static void removeChunk(FreeList* ptr) {
    // using the logic from HW1 to remove element from a doubly linked list
    ptr->prev->next = ptr->next;
    ptr->next->prev = ptr->prev;
    // update chunk's pointers to free
    ptr->next = NULL;
    ptr->prev = NULL;
}

/*----------------------------------------------------------------------------------*/
/*
 * free: frees block pointed by ptr; no return value; add free chunk to appropriate freeList
 * Overview: success when
 * 1. ptr was returned earlier by malloc(), calloc(), or realloc() &&
 * 2. ptr has not been freed
 * If ptr == NULL, then do nothing and print error statement
 */
void free(void* ptr)
{
    // check if ptr is valid
    if (ptr==NULL) {
        perror("Invalid ptr passed in free()\n");
        return;
    }

    // size of hdr
    size_t size = ptrSize(hdr(ptr));
    
    // [1. if ptr has already been freed earlier, return]
    if(!allocatedBit(hdr(ptr))) {
        perror("Ptr has already been freed\n");
        return;
    } 
    // [2. ptr has not been freed, need to free and coalese ]
    // free the chunk ptr in hdr
    *(size_t*)hdr(ptr) = size | 0;
    *(size_t*)ftr(ptr) = size | 0;

    // if a block is freed, update the next chunk's prevAlloc bit = 0 
    updateNext(prevChunk(ptr));

    // coalesce using the helper function since I freed the chunk  
    coalesce(ptr);
}

/* Helper Function to add the newly freed chunk to proper freeList*/
static void addChunk(FreeList *newChunk, FreeList *fl) {
    // inserting new chunk into a doubly linked list (same logic as previous implementation)
    newChunk->next = fl->next;
    newChunk->prev = fl;
    fl->next->prev = newChunk;
    fl->next = newChunk;
}

/* Helper Function to coalesce neighboring free blocks: mitigate fragmentation 
    (referring to the slides from class and advice from Prof) */
static void *coalesce(void *ptr) {
    // check if ptr is valid
    if (ptr == NULL) {
        perror("Invalid ptr passed in coalesce()\n");
    }

    // size to header of this chunk
    size_t size = ptrSize(hdr(ptr)); 
    // variables to keep prev and next chunk's allocatedBit flag
    size_t prevAlloc = allocatedBit(hdr(prevChunk(ptr)));
    size_t nextAlloc = allocatedBit(hdr(nextChunk(ptr)));
    // keeping var to correct fl so I don't have to keep making one
    FreeList *fl = getFl(getFlIndex(size));

    // [1. if previous and next chunk is alloc --> no coalescing:)]
    if (prevAlloc && nextAlloc) {
        addChunk(ptr, fl);
        updateNext(ptr);
        return ptr;
    }
    // [2. if next chunk is free, but previous chunk is not, coalesce this chunk with next chunk]
    else if(prevAlloc && !nextAlloc) {
        // update the size 
        size += ptrSize(hdr(nextChunk(ptr))); 
        // remove the next chunk from freeList
        removeChunk(nextChunk(ptr));
        // merge
        *(size_t *)hdr(ptr) = size | 0; 
        *(size_t *)ftr(ptr) = size | 0;
        // find correct free list to add chunk to and then add it to that
        fl = getFl(getFlIndex(size));
        addChunk(ptr, fl);
    } 
    // [3. if previous chunk is free, but next chunk is not, coalesce prev chunk with this chunk]
    else if (!prevAlloc && nextAlloc) {
        // update the size 
        size += ptrSize(hdr(prevChunk(ptr))); 
        // remove the prev chunk
        removeChunk(prevChunk(ptr));
        // merge
        *(size_t *)ftr(ptr) = size | 0; 
        *(size_t *)hdr(prevChunk(ptr)) = size | 0; 
        // update ptr to point to previous chunk
        ptr = prevChunk(ptr);  
        // find correct free list to add chunk to and then add it to that
        fl = getFl(getFlIndex(size));
        addChunk(ptr, fl);
    }
    // [4. if previous and next chunk is not alloc, coalesce all chunks]
    else {
        size += ptrSize(hdr(prevChunk(ptr))) + ptrSize(ftr(nextChunk(ptr)));
        // remove previous and next chunk from freeList
        removeChunk(prevChunk(ptr));
        removeChunk(nextChunk(ptr));
        // merge
        *(size_t *)hdr(prevChunk(ptr)) = size | 0; 
        *(size_t *)ftr(nextChunk(ptr)) = size | 0; 
        // update ptr to point to previous chunk
        ptr = prevChunk(ptr);
        // find correct free list to add chunk to and then add it to that
        fl = getFl(getFlIndex(size));
        addChunk(ptr, fl);
        // update nxt chunk's prevAllocatedBit
        updateNext(prevChunk(ptr));
    }

    // update nxt chunk's prevAllocatedBit
    updateNext(ptr);
    // return the proper chunk after coalescing
    return ptr;
}

/*----------------------------------------------------------------------------------*/
/*
 * realloc: returns ptr to allocated regiod of size bytes
 * Overview: 1. if ptr==NULL, then call malloc(size)
 *           2. if size==0, then call free(ptr) and return NULL
 *           3. if ptr!=NULL, then ptr has to be returned earlier by malloc(), calloc(), or realloc()
 */
void* realloc(void* oldptr, size_t size)
{
    // [1. if oldptr == NULL]
    if (oldptr==NULL) {
       // call malloc(size) and return the newPtr
       return malloc(size);
    }
    // [2. if size == 0]
    else if (size == 0){
        // call free(ptr) and return NULL
        free(oldptr);
        return NULL;
    }
    // [3. if ptr != NULL]
    else {
        // store size of oldptr and create new ptr
        size_t oldSize = ptrSize(hdr(oldptr));

        // i) if the old ptr is less than 'size' requested, I can just use the oldptr
        if (size <= oldSize) {
            // return  heap until that point
            void *newPtr = malloc(oldSize);
            if (newPtr == NULL)
            {
                return NULL;
            }
            mm_memcpy(newPtr, oldptr, size);
            free(oldptr);
            return newPtr;
            // return oldptr;
        }

        // ii) has to be returned earlier by malloc(), calloc(), or realloc() 
        else {
            // find bigger size
            void *newPtr = malloc(size);

            // check if malloc(size) failed
            if (newPtr == NULL) {
                perror("malloc() failed in realloc()\n");
                return NULL;
            }

            // check the appropriate size I'm copying using ternary operator
            size_t copySize = (size < oldSize)? size : oldSize;
            mem_memcpy(newPtr, oldptr, copySize); 
            free(oldptr);

            //return new ptr
            return newPtr;
        }
    }
    
    return NULL;
}

/*----------------------------------------------------------------------------------*/
/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size)
{
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}

/*----------------------------------------------------------------------------------*/
/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p)
{
    return p <= mm_heap_hi() && p >= mm_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*
 * mm_checkheap: Heap Consistency Checker that checks 'invariants'
 * You call the function via mm_checkheap(__LINE__)
 * The line number can be used to print the line number of the calling
 * function where there was an invalid heap.
 */
bool mm_checkheap(int line_number)
{
    printf("mm_checkheap at line: %d\n", line_number);
#ifdef DEBUG
    /* Using invariant questions from the README for this checkpoint to guide */

    // Is the start of the heap valid?
    char *pro = heapStart;
    if(ptrSize(hdr(pro)) != 16) {
        printf("Start of heap is not valid\n");
    }
    
    pro = heapStart; //ptr to the start of freeList
    
    while(ptrSize(hdr(pro)) >  (size_t) 0) {
        // Is every block in the free list marked as free? 
        if(allocatedBit(pro)) {
            printf("%p is not marked as free\n", (void*)pro);
            return false;
        }

        // Are there any contiguous free blocks that somehow escaped coalescing?
        if(!allocatedBit(nextChunk(pro))) { // is contiguous chunk free?
            if(!allocatedBit(pro)) { // is this chunk free?
                printf("%p is not coalesced with %p\n", (void*)pro, nextChunk(pro));
                return false;
            }
        }

        // Is every free block actually in the free list?
        if(!in_heap(pro) || in_heap(hdr(pro)) || !in_heap(ftr(pro))) { // check if chunk is in freeList
           printf("%p chunk is not in heap\n", (void*)pro);
           return false;
        }

        // Do any allocated blocks overlap?
        if(hdr(nextChunk(pro)) < ftr(pro)) {
            printf("%p and %p chunks overlap\n", (void*)pro, nextChunk(pro));
            return false;
        }

        // Do the pointers in the free list point to valid free blocks?
        if (pro < heapStart) { // chunk is before heap :/
            printf("%p is not in heap\n", pro);
            return false;
        }
        if (allocatedBit(pro)) {
            printf("%p is allocated but is in the free list\n", (char*)pro);
            return false;
        }

        //move to next free chunk
        pro = nextChunk(pro); 
    }
    
#endif // DEBUG
    return true;
}