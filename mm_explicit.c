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
// explicit
#include <sys/mman.h> // 메모리 관리 관련 헤더
#include <errno.h> // 정적 메모리 위치에 저장된 오류 코드를 통해 오류 상태를 보고 및 검색하기 위한 매크로를 정의

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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

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

/* explicit에서 추가한 부분  */
#define PRED_FREEP(bp) (*(void**)(bp)) // 
#define SUCC_FREEP(bp) (*(void**)(bp+WSIZE))

// Declaration
static void *heap_listp; // heap 시작 주소 pointer
static void *free_listp; // free list head - 가용 리스트 시작 부분
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t a_size);
static void place(void *bp, size_t a_size);
/* explici 구현을 위해 추가한 부분 */
void removeBlock(void *bp);
void putFreeBlock(void *bp);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    heap_listp = mem_sbrk(24); // 24byte를 늘려주고, 함수의 시작 부분을 가리키는 주소를 반환, mem_brk는 끝에 가있음
    /* Create the initial empty heap */
    if(heap_listp == (void *)-1)
        return -1;

    PUT(heap_listp, 0); // 사용하지 않는 padding                   
    PUT(heap_listp+WSIZE, PACK(16,1)); // 프롤로그 헤더
    PUT(heap_listp + 2*WSIZE, NULL);  // 프롤로그 pred 포인터를 null로 초기화
    PUT(heap_listp + 3*WSIZE, NULL); // 프롤로그 succ 포인터를 null로 초기화
    PUT(heap_listp + 4*WSIZE, PACK(16, 1)); // 프롤로그 풋터
    PUT(heap_listp + 5*WSIZE, PACK(0,1)); // 에필로그 헤더

    free_listp = heap_listp + DSIZE; // free_listp를 pred 포인터를 가리키게 초기화

    if(extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1; 
    return 0;
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    /* case 1 - 가용 블록이 없으면 조건을 추가할 필요 없음 */
    /* case 2 */
    if(prev_alloc && !next_alloc)
    {
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    /* case 3 */
    else if(!prev_alloc && next_alloc)
    {
        removeBlock(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    /* case 4 */
    else if(!prev_alloc && !next_alloc)
    {
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    putFreeBlock(bp);
    return bp;

}
// extend heap 함수
// 1. heap이 초기화될때 다음 블록을 CHUNKSIZE만큼 미리 할당해준다.
// 2. mm_malloc이 적당한 맞춤을 찾지 못했을때 CHUNKSIZE만큼 할당해준다.
// 
// heap을 CHUNKSIZE byte로 확장하고 초기 가용 블록을 생성한다.
// 여기까지 진행되면 할당기는 초기화를 완료하고, application으로부터 할당과 반환 요청을 받을 준비를 완료하였다.
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 블록을 짝수개만큼 할당 (한번에 2워드씩 할당하므로)
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if (((bp = mem_sbrk(size)) == (void*)-1))
    {
        return NULL;
    }
    // 할당한 블록에 header, footer를 설정해주고 에필로그를 설정해줌
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    

    return coalesce(bp);
}

static void *find_fit(size_t asize) // first fit으로 검색을 함
{
    void *bp;
    // 가용 리스트 내부의 유일한 할당 블록인 프롤로그 블록을 만나면 종료
    for(bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC_FREEP(bp))
    {
        if(GET_SIZE(HDRP(bp)) >= asize)
        {
            return bp;
        }
    }
    return NULL;

}

/*
    데이터를 할당할 가용 블록의 bp와 배치 용량 할당
*/
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    // 할당 블록은 freelist에서 지운다.
    removeBlock(bp);
    if((csize - asize) >= (2*DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        putFreeBlock(bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    
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

    /* Ignore spurious request */
    if (size <= 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else    
        asize = DSIZE *((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    if ((bp = find_fit(asize)) != NULL) {
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
// putFreeBlock 함수 
// 새로운 블록을 넣고 그에따른 pred포인터와 succ의 포인터를 변경해주는 함수
void putFreeBlock(void *bp)
{
    SUCC_FREEP(bp) = free_listp;
    PRED_FREEP(bp) = NULL;
    PRED_FREEP(free_listp) = bp;
    free_listp = bp;
}
// removeBlock 함수
// splice out 해주는 함수
void removeBlock(void *bp)
{
    if(bp == free_listp)
    {
        PRED_FREEP(SUCC_FREEP(bp)) = NULL;
        free_listp = SUCC_FREEP(bp);
    } else {
        SUCC_FREEP(PRED_FREEP(bp)) = SUCC_FREEP(bp);
        PRED_FREEP(SUCC_FREEP(bp)) = PRED_FREEP(bp);
    }
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


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    if(size <= 0){
        mm_free(bp);
        return 0;
    }
    if(bp == NULL){
        return mm_malloc(size);
    }
    void *newp = mm_malloc(size);
    if(newp == NULL){
        return 0;
    }
    size_t oldsize = GET_SIZE(HDRP(bp));
    if(size < oldsize){
        oldsize = size;
    }
    memcpy(newp, bp, oldsize);
    mm_free(bp);
    return newp;
}

