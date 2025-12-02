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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~(ALIGNMENT - 1))

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*
 *  < Allocated Block >
 * [ Block size | alloc ] Header - 1 Words
 * [ Playload           ] (allocated block only)
 * [ Padding            ] (optioanal)
 * [ Block size | alloc ] Footer - 1 Words
 *
 * < Free Block >
 * [ Block size | alloc ] Header - 1 Words
 * [ Predecessor        ] (old payload)
 * [ Successor          ] (old payload)
 * [ Padding            ] (optioanal)
 * [ Block size | alloc ] Footer - 1 Words
 *
 */

// Basic constants and macros
#define MAX_POWER 50 // 2의 최대 몇 제곱까지 사이즈 클래스를 지원할지. 여기에서는 2^50까지의 사이즈 클래스를 지원함
#define TAKEN 1
#define FREE 0
#define WORD 4
#define DWORD 8
#define CHUNK ((1 << 12) / WORD)
#define STATUS_BIT_SIZE 3 // 할당된 블록과 할당되지 않은 블록을 구분하기 위해 사용되는 비트의 크기
#define HDR_FTR_SIZE 2    // 단위: word
#define HDR_SIZE 1        // 단위: word
#define FTR_SIZE 1        // 단위: word
#define PRED_FIELD_SIZE 1 // 단위: word
#define EPILOG_SIZE 2     // 단위: word
#define ALIGNMENT 8

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 주소 p에 적힌 값을 읽어오기 */
#define GET_WORD(p) (*(unsigned int *)(p))

/* 주소 p에 새로운 값을 쓰기*/
#define PUT(p, val) (*(char **)(p) = (val))

/* size보다 크면서 가장 가까운 ALIGNMENT의 배수 찾기 */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~(ALIGNMENT - 1))

/* x보다 크면서 가장 가까운 짝수 찾기 */
#define EVENIZE(x) ((x + 1) & ~1)

/* 주어진 사이즈의 비트 마스크 생성하기 */
#define GET_MASK(size) ((1 << size) - 1)

/* 블록 사이즈 가져오기 */
#define GET_SIZE(p) ((GET_WORD(p) & ~GET_MASK(STATUS_BIT_SIZE)) >> STATUS_BIT_SIZE)

/* 블록의 할당 여부 가져오기 */
#define GET_STATUS(p) (GET_WORD(p) & 0x1)

/*
 * 블록의 크기와 할당 비트를 통합해서 header와 footer에 저장할 수 있는 값 만들기
 * Pack a size and allocated bit into a word
 */
#define PACK(size, status) ((size << STATUS_BIT_SIZE) | (status))

/*
 * 블록 헤더의 주소 가져오기
 */
#define HDRP(bp) ((char *)(bp)-WSIZE)

/* 블록 푸터의 주소 가져오기 */
#define FTRP(header_p) ((char **)(header_p) + GET_SIZE(header_p) + HDR_SIZE)

/* 헤더와 푸터를 포함한 블록의 사이즈 가져오기 */
#define GET_TOTAL_SIZE(p) (GET_SIZE(p) + HDR_FTR_SIZE)

/* free_lists의 i번째 요소 가져오기 */
#define GET_FREE_LIST_PTR(i) (*(free_lists + i))

/* free_lists의 i번째 요소 값 설정하기 */
#define SET_FREE_LIST_PTR(i, ptr) (*(free_lists + i) = ptr)

/* 가용 블록의 predecessor, successor 주소값 셋팅 */
#define SET_PTR(p, ptr) (*(char **)(p) = (char *)(ptr))

/* 가용 블록 내에 predecessor 주소가 적힌 곳의 포인터 가져오기 */
#define GET_PTR_PRED_FIELD(ptr) ((char **)(ptr) + HDR_SIZE)

/* 가용 블록 내에 successor 주소가 적힌 곳의 포인터 가져오기 */
#define GET_PTR_SUCC_FIELD(ptr) ((char **)(ptr) + HDR_SIZE + PRED_FIELD_SIZE)

/* 가용 블록의 predecessor 메모리 공간에 저장된 주소값 가져오기 */
#define GET_PRED(bp) (*(GET_PTR_PRED_FIELD(bp)))

/* 가용 블록의 successor 메모리 공간에 저장된 주소값 가져오기 */
#define GET_SUCC(bp) (*(GET_PTR_SUCC_FIELD(bp)))

/* 이전 블록의 포인터 가져오기 */
#define PREV_BLOCK_IN_HEAP(header_p) ((char **)(header_p)-GET_TOTAL_SIZE((char **)(header_p)-FTR_SIZE))

/* 다음 블록의 포인터 가져오기 */
#define NEXT_BLOCK_IN_HEAP(header_p) (FTRP(header_p) + FTR_SIZE)

static char **free_lists;
static char **heap_ptr;
// static int previous_size;

static void *extend_heap(size_t words);
static void place(char **bp);
static int round_up_power_2(int x);
static int round_to_thousand(size_t x);
static size_t find_free_list_index(size_t words);
static void *find_free_block(size_t words);
static void insert_block(void *bp, size_t words);
static void remove_block(char **bp);
static void *coalesce(void *bp);
void *mm_realloc_wrapped(void *ptr, size_t size, int buffer_size);


void insert_block(void *bp, size_t words) {
    debug("Start");
    size_t bp_tot_size = GET_SIZE(bp) + HDR_FTR_SIZE;
    size_t needed_size = words;
    size_t needed_tot_size = needed_size + HDR_FTR_SIZE;
    size_t left_block_size = bp_tot_size - needed_tot_size - HDR_FTR_SIZE;

    char **new_block_ptr;

    if ((int)left_block_size > 0) {
        PUT(bp, PACK(needed_size, TAKEN));
        PUT(FTRP(bp), PACK(needed_size, TAKEN));

        new_block_ptr = (char **)(bp) + needed_tot_size;

        PUT(new_block_ptr, PACK(left_block_size, FREE));
        PUT(FTRP(new_block_ptr), PACK(left_block_size, FREE));

        new_block_ptr = coalesce(new_block_ptr);
        place(new_block_ptr);
    } else if (left_block_size == 0) {
        PUT(bp, PACK(needed_tot_size, TAKEN));
        PUT(FTRP(bp), PACK(needed_tot_size, TAKEN));
    } else {
        PUT(bp, PACK(needed_size, TAKEN));
        PUT(FTRP(bp), PACK(needed_size, TAKEN));
    }
    debug("End");
}

void remove_block(char **bp) {
    debug("Start");
    char **prev_block = GET_PRED(bp);
    char **next_block = GET_SUCC(bp);
    int index = 0;

    if (GET_SIZE(bp) == 0) {
        debug("End 0");
        return;
    }

    if (prev_block == NULL) {
        index = find_free_list_index(GET_SIZE(bp));
        GET_FREE_LIST_PTR(index) = next_block;
    } else {
        SET_PTR(GET_PTR_SUCC_FIELD(prev_block), next_block);
    }

    if (next_block) {
        SET_PTR(GET_PTR_PRED_FIELD(next_block), prev_block);
    }

    SET_PTR(GET_PTR_PRED_FIELD(bp), NULL);
    SET_PTR(GET_PTR_SUCC_FIELD(bp), NULL);
    debug("End");
}

static void *coalesce(void *bp) {
    debug("Start");
    char **prev_block = PREV_BLOCK_IN_HEAP(bp);
    char **next_block = NEXT_BLOCK_IN_HEAP(bp);
    size_t prev_status = GET_STATUS(prev_block);
    size_t next_status = GET_STATUS(next_block);
    size_t new_size = GET_SIZE(bp);

    if (prev_status == TAKEN && next_status == TAKEN) {
        debug("End");
        return bp;
    } else if (prev_status == TAKEN) {
        remove_block(next_block);
        new_size += GET_TOTAL_SIZE(next_block);
        PUT(bp, PACK(new_size, FREE));
        PUT(FTRP(next_block), PACK(new_size, FREE));
    } else if (next_status == TAKEN) {
        remove_block(prev_block);
        new_size += GET_TOTAL_SIZE(prev_block);
        PUT(prev_block, PACK(new_size, FREE));
        PUT(FTRP(bp), PACK(new_size, FREE));
        bp = prev_block;
    } else {
        remove_block(prev_block);
        remove_block(next_block);
        new_size += GET_TOTAL_SIZE(prev_block) +
                    GET_TOTAL_SIZE(next_block);
        PUT(prev_block, PACK(new_size, FREE));
        PUT(FTRP(next_block), PACK(new_size, FREE));
        bp = prev_block;
    }
    debug("End");

    return bp;
}

static void *extend_heap(size_t words) {
    debug("Start");
    char **bp;
    char **end_ptr;
    size_t words_extend = EVENIZE(words);
    size_t words_extend_total = words_extend + HDR_FTR_SIZE;

    if ((bp = mem_sbrk(words_extend_total * WORD)) == -1)
        return NULL;

    bp -= EPILOG_SIZE;

    PUT(bp, PACK(words_extend, FREE));
    PUT(FTRP(bp), PACK(words_extend, FREE));

    end_ptr = bp + words_extend_total;
    PUT(end_ptr, PACK(0, TAKEN));
    PUT(FTRP(end_ptr), PACK(0, TAKEN));
    debug("End");
    return bp;
}

static size_t find_free_list_index(size_t words) {
    debug("Start");
    int index = 0;
    while ((index <= MAX_POWER) && (words > 1)) {
        words >>= 1;
        index++;
    }
    debug("End");
    return index;
}

static void *find_fit(size_t words) {
    debug("Start");
    char **bp;
    size_t index = find_free_list_index(words);

    while (index <= MAX_POWER) {
        if ((bp = GET_FREE_LIST_PTR(index)) && GET_SIZE(bp) >= words) {
            while (true) {
                if (GET_SIZE(bp) == words) {
                    debug("End");
                    return bp;
                }

                if (GET_SUCC(bp) == NULL || GET_SIZE(GET_SUCC(bp))) {
                    debug("End");
                    return bp;
                }

                bp = GET_SUCC(bp);
            }
        }

        index++;
    }

    return NULL;
}

static void place(char **bp) {
    debug("Start");
    size_t size = GET_SIZE(bp);
    if (size == 0) {
        debug("End 0");
        return;
    }

    int index = find_free_list_index(size);
    char **front_ptr = GET_FREE_LIST_PTR(index);
    char **prev_ptr = NULL;

    if (front_ptr == NULL) {
        SET_PTR(GET_PTR_PRED_FIELD(bp), NULL);
        SET_PTR(GET_PTR_SUCC_FIELD(bp), NULL);
        SET_FREE_LIST_PTR(index, bp);
        debug("End");
        return;
    }

    if (size >= GET_SIZE(front_ptr)) {
        SET_FREE_LIST_PTR(index, bp);
        SET_PTR(GET_PTR_PRED_FIELD(bp), NULL);
        SET_PTR(GET_PTR_SUCC_FIELD(bp), front_ptr);
        SET_PTR(GET_PTR_SUCC_FIELD(front_ptr), bp);
        debug("End");
        return;
    }

    while (front_ptr && GET_SIZE(front_ptr) > size) {
        prev_ptr = front_ptr;
        front_ptr = GET_SUCC(front_ptr);
    }

    if (front_ptr == NULL) {
        SET_PTR(GET_PTR_SUCC_FIELD(prev_ptr), bp);
        SET_PTR(GET_PTR_PRED_FIELD(bp), prev_ptr);
        SET_PTR(GET_PTR_SUCC_FIELD(bp), NULL);
        debug("End");
        return;
    }

    SET_PTR(GET_PTR_SUCC_FIELD(prev_ptr), bp);
    SET_PTR(GET_PTR_PRED_FIELD(bp), prev_ptr);
    SET_PTR(GET_PTR_SUCC_FIELD(bp), front_ptr);
    SET_PTR(GET_PTR_PRED_FIELD(front_ptr), bp);
    debug("End");
}

static int round_up_power_2(int x) {
    if (x < 0)
        return 0;

    --x;
    x |= x >> 1;
    x |= x >> 2;
    x |= x >> 4;
    x |= x >> 8;
    x |= x >> 16;
    return x + 1;
}

static int round_to_thousand(size_t x) {
    return x % 1000 >= 500 ? x + 1000 - x % 1000 : x - x % 1000;
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    debug("Start");
    if ((free_lists = mem_sbrk(MAX_POWER * sizeof(char *))) == -1)
        return -1;

    for (int i = 0; i <= MAX_POWER; i++)
        SET_FREE_LIST_PTR(i, NULL);

    mem_sbrk(WORD);

    if ((heap_ptr = mem_sbrk(4 * WORD)) == -1)
        return -1;

    PUT(heap_ptr, PACK(0, TAKEN));
    PUT(FTRP(heap_ptr), PACK(0, TAKEN));

    char **epilogue = NEXT_BLOCK_IN_HEAP(heap_ptr);
    PUT(epilogue, PACK(0, TAKEN));
    PUT(FTRP(epilogue), PACK(0, TAKEN));

    heap_ptr = NEXT_BLOCK_IN_HEAP(heap_ptr);

    char **new_block;
    if ((new_block = extend_heap(CHUNK)) == NULL)
        return -1;

    place(new_block);
    debug("End");
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    debug("Start");
    if (size <= 0)
        return NULL;

    if (size <= CHUNK * WORD)
        size = round_up_power_2(size);

    size_t words = ALIGN(size) / WORD;

    size_t extendsize;
    char **bp;

    if ((bp = find_fit(words))) {
        remove_block(bp);
        insert_block(bp, words);
        debug("End");
        return bp + HDR_SIZE;
    }

    // No fit found -> Get more memory and place the block
    extendsize = MAX(words, CHUNK);
    if ((bp = extend_heap(extendsize)) == NULL)
        return (void *)NULL;

    insert_block(bp, words);
    debug("End");
    return bp + HDR_SIZE;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    debug("Start");
    ptr -= WORD; // header
    size_t size = GET_SIZE(ptr);
    PUT(ptr, PACK(size, FREE));
    PUT(FTRP(ptr), PACK(size, FREE));

    ptr = coalesce(ptr);
    place(ptr);
    debug("End");
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
