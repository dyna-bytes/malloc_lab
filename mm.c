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
#include <stdbool.h>

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
    "Jihyuk Park",
    /* First member's email address */
    "jihyuk3885@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

#define DBG
#ifdef DBG
#define debug(x) printf("[%s](%d) %s is %d\n", __func__, __LINE__, #x, x)
#else
#define debug(x)
#endif

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*
 * [ Block size | alloc ] Header - 1 Words
 * [ Playload           ] (allocated block only)
 * [ Padding            ] (optioanal)
 * [ Block size | alloc ] Footer - 1 Words
 */

// Basic constants and macros
#define WSIZE 4 /* Bytes */
#define DSIZE 8 /* Bytes */
#define CHUNKSIZE (1 << 12) /* 2^12 Bytes */
#define MINBLOCKSIZE 2 * DSIZE

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the szie and alloctated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previout blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static char *heap_listp;
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);


static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        return bp;
    } else if (prev_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, false)); // Set Free
        PUT(FTRP(bp), PACK(size, false)); // Set Free
    } else if (next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, false));
        PUT(FTRP(bp), PACK(size, false));
        bp = PREV_BLKP(bp);
    } else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, false));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, false));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    debug(words);
    // Always use even size of words to keep alignment
    size = (words + 1) / 2 * DSIZE;
    if ((bp = mem_sbrk(size)) == (void *)-1)
        return NULL;
    debug(size);

    // Initialize Header and Footer of new free block
    PUT(HDRP(bp), PACK(size, false)); // Free block header <= Previous Old Epilogue Header
    PUT(FTRP(bp), PACK(size, false)); // Free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, true)); // New epilogue header

    // Coalesce if the previous block was free
    return coalesce(bp);
}

static void *find_fit(size_t asize) {
    for (void *bp = heap_listp; GET_SIZE(HDRP(bp)); bp = NEXT_BLKP(bp))
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;

    return NULL;
}

static void place(void *bp, size_t size) {
    size_t block_size = GET_SIZE(HDRP(bp));

    if ((block_size - size) >= MINBLOCKSIZE) {
        PUT(HDRP(bp), PACK(size, true));
        PUT(FTRP(bp), PACK(size, true));

        // Internal Fragmentation
        PUT(HDRP(NEXT_BLKP(bp)), PACK(block_size - size, false));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(block_size - size, false));
    } else {
        // Internal Fragmentation
        PUT(HDRP(bp), PACK(block_size, true));
        PUT(FTRP(bp), PACK(block_size, true));
    }
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0); // Alignment padding
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, true)); // Prolouge Header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, true)); // Prolouge Footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, true)); // Epilouge Header

    heap_listp += (2 * WSIZE); // Point Prolouge Footer
    /*
     * [     | 16/0 | 16/0 | 8/1 ]
     *    ^      ^      ^     ^
     * unused  start    bp   end
    */

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) // 2^12 / 4 = 1024 Bytes
        return -1;
    /*
     * [     | 16/0 | 16/0 | (1024 B) | 8/1 ]
     *                  ^
     *                  bp
    */

    return 0;
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

    if (size <= 0)
        return NULL;

    // Adjust block size to include overhead and alignment reqs.
    if (size <= DSIZE)
        asize = MINBLOCKSIZE;
    else
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

    if ((bp = find_fit(asize))) {
        place(bp, asize); // if possible, split remaininig parts
        return bp;
    }

    // No fit found -> Get more memory and place the block
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return (void *)-1;
    place(bp, extendsize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, false));
    PUT(FTRP(bp), PACK(size, false));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
