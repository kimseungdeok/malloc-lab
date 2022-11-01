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
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "team4",
    /* First member's full name */
    "kimseungdeok",
    /* First member's email address */
    "tmdejr1117@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* Basic constants and macros */
/*macros*/
#define WSIZE 4             // word and header/footer size(bytes)
#define DSIZE 8             // double word size(bytes)
#define CHUNKSIZE (1 << 12) // heap 확장 : 4096 byte

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // 최댓값 구하기

/*header에 들어가는 값(size and allocated bit)를 한 워드로*/
// #define PACK (size, alloc) ((size) | (alloc))
#define PACK(size, alloc) ((size) | (alloc))

/*p가 가리키는 워드 읽어오기, p가 가리키는 워드에 값 넣기*/
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/*header 에서 size field, allocated field 읽어오기*/
#define GET_SIZE(p) (GET(p) & ~0x7) //블럭크기 읽어오기
#define GET_ALLOC(p) (GET(p) & 0x1) //해당 블럭의 할당여부 읽어오기 1 : allocated, 0:free

/*블록 header 와 footer를 가리키는 포인터 return*/
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/*다음과 이전블록의 블록포인터 리턴*/
#define NEXT_BLKP(bp) (((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) (((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE)))

// Declaration
static void *heap_listp;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *best_fit(size_t asize); // best fit
static void place(void *bp, size_t a_size);


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);
    

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    
    return 0;
}

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    /* Ignore spurious request */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else    
        asize = DSIZE *((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    if ((bp = best_fit(asize)) != NULL) {
        place(bp, asize);
        
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    
    return bp;

}

// static void *next_fit(size_t asize)
// {
//     char *bp = last_bp;

//     for (bp = NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) != 0; bp = NEXT_BLKP(bp))
//     {
//         if(!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize)
//         {
//             last_bp = bp;
//             return bp;
//         }
//     }

//     bp = heap_listp;
//     while(bp < last_bp)
//     {
//         bp = NEXT_BLKP(bp);
//         if(!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize)
//         {
//             last_bp = bp;
//             return bp;
//         }
//     }
//     return NULL;
// }

static void *best_fit(size_t asize)
{
       char *bp;
    char *best_bp = NULL;
    size_t best_size;
    size_t min = SIZE_MAX;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){ // GET_SIZE(HDRP(bp)) > 0 ; 에필로그 가기 전까지


        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            best_size = asize - GET_SIZE(HDRP(bp));

            if (best_size == 0){
                return bp;
            }    

            if (best_size < min) {
                min = best_size;
                best_bp = bp;
            } 
        }
    }

    if (best_bp == NULL) {
        return NULL;
    }

    return best_bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}


static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        return NULL;
    }
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    
    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc) /* Case 1 */
    {  
        
        return bp;
    }

    else if(prev_alloc && !next_alloc) /* Case 2 */
    { 
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) /* Case 3 */
    { 
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else                               /* Case 4 */
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    return bp;


}

/*
    데이터를 할당할 가용 블록의 bp와 배치 용량 할당
*/
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if((csize - asize) >= (2*DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    size_t old_size = GET_SIZE(HDRP(bp));
    size_t new_size = size + (2 * WSIZE);

    if(new_size <= old_size)
    {
        return bp;
    }
    else
    {
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
        size_t csize = old_size + GET_SIZE(HDRP(NEXT_BLKP(bp)));

        if(!next_alloc && csize >= new_size)
        {
            PUT(HDRP(bp), PACK(csize, 1));
            PUT(FTRP(bp), PACK(csize, 1));
            return bp;
        }
        else
        {
            void *new_bp = mm_malloc(new_size);
            place(new_bp, new_size);
            memcpy(new_bp, bp, new_size);
            mm_free(bp);
            return new_bp;
        }
    }
}

