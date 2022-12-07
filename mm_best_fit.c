/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// macro
#define WSIZE 4 //word and header, footer size is 4 bytes
#define DSIZE 8 //double word size is 8 bytes
#define CHUNKSIZE (1<<12) //add heap 4kb
#define MAX(x, y) ((x)>(y)? (x) : (y)) //get bigger value
#define PACK(size, alloc) ((size) | (alloc)) // alloc : is it allocated ? // size : block size
#define GET(p) (*(unsigned int*)(p)) //reference p by pointer, you can use it to point to another block or to move another block
#define PUT(p, val) (*(unsigned int*)(p) = (int)(val)) //Saving the block's address, when you read the header or footer for moving or connecting, can be used it
#define GET_SIZE(p) (GET(p) & ~0x7) //only get block size by bit oper
#define GET_ALLOC(p) (GET(p) & 0x1) //get alloc stats (0 or 1)
#define HDRP(bp) ((char*)(bp) - WSIZE) //header pointer is in front of the WSISE
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //(end of header) + (block size) - (double word size) = start of footer
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp)-WSIZE))) // move to next block bp position
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE))) // move to prev block bp position
static char *heap_listp; //init_available block heap

// function
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void*)-1) { // alloc first heap sector
        return -1;
    }
    PUT(heap_listp, 0); //create padding
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // create prologue header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // create prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); // create epilogue block header
    heap_listp += (2*WSIZE); // move point between prologue header and footer

    if(extend_heap(CHUNKSIZE/WSIZE)==NULL) {
        return -1;
    }
    return 0;
}

static void *extend_heap(size_t words) { //case 1 = init_heap, case 2 = need more heap (can't find suitable sector)
    char *bp;
    size_t size;
    size = (words%2) ? (words+1) * WSIZE : words * WSIZE; // maintain even 
    if((long)(bp=mem_sbrk(size)) == -1){
        return NULL;
    }

    PUT(HDRP(bp), PACK(size, 0)); //create free block header
    PUT(FTRP(bp), PACK(size, 0)); // free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); //adjust epilogue header

    return coalesce(bp);
}

static void *coalesce(void *bp) { //To prevent false fragmentation 
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); //check availability of previous blocks
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); //check availability of next blocks
    size_t size = GET_SIZE(HDRP(bp)); //check size of now blocks

    if(prev_alloc && next_alloc) { //can't coalesce
        return bp;
    }
    else if(prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); //refresh now -> prev + now 
        PUT(HDRP(bp), PACK(size, 0)); //refresh header info
        PUT(FTRP(bp), PACK(size, 0)); //refresh footer info
    }
    else if(!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0)); //adjust footer
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); //change header position and input new size(now + next)
        bp = PREV_BLKP(bp); //move bp to front block's header
    }
    else { //coalesce 3 blocks
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if(size == 0) return NULL; //no alloc
    //set block size
    if(size <= DSIZE) { //adjust block size (including header and footer)
        asize = 2*DSIZE;
    }
    else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); //if size > DSIZE : optimalize block size
    }
    //find proper empty space
    if((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    extendsize = MAX(asize, CHUNKSIZE); // chunksize -> default size (programmer setting)
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize); //put asize in extended status
    return bp;
}

static void *find_fit(size_t asize) { //best fit
    void *bp;
    void *result;
    int bit = 0;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) { //start : heap_listp, end : epilogue
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) { // size ok, unallocated true
            if(bit == 0) {
                result = bp;
            }
            if(GET_SIZE(result) > GET_SIZE(HDRP(bp))) {
                result = bp;
            }
            bit = 1;
        }
    }
    if (bit == 1) return result;
    return NULL;
}

static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp)); //now block size
    if((csize-asize) >= (2*DSIZE)) { //check (block size) - asize > 2*DSIZE (header + footer minimum size) is true ?
        PUT(HDRP(bp), PACK(asize, 1)); //header location <- input asize and make status 1 (alloc) // refresh headersize -> asize
        PUT(FTRP(bp), PACK(asize, 1)); //modify footer location
        bp = NEXT_BLKP(bp); //refresh bp location
        PUT(HDRP(bp), PACK(csize-asize, 0)); // (csize-asize) -> remain space -> display it can be allocated
        PUT(FTRP(bp), PACK(csize-asize, 0)); // also display at footer
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1)); // else case, use all block
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr)); // release size
    PUT(HDRP(ptr), PACK(size, 0)); //header release
    PUT(FTRP(ptr), PACK(size, 0)); // footer release
    coalesce(ptr);

}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if(size <= 0) {
        mm_free(ptr);
        return 0;
    }
    if(ptr == NULL) {
        return mm_malloc(size);
    }
    void *newp = mm_malloc(size);
    if(newp == NULL) {
        return 0;
    }
    size_t oldsize = GET_SIZE(HDRP(ptr));
    if(size < oldsize) {
        oldsize = size;
    }
    memcpy(newp, ptr, oldsize);
    mm_free(ptr);
    return newp;
}