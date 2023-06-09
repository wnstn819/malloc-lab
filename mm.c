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
/* 더블워드 크기 */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */

#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
/* 워드와 헤더 푸터 크기 */
#define WSIZE   4   /* Word and header/footer size(bytes) */
/* 더블 워드 크기 */
#define DSIZE   8   /* Doulble word size(bytes) */
#define CHUNKSIZE   (1<<12) /* 한 확장을 위한 기본 크기 */


/* x,y의 크기 중 큰거 반환 */
#define MAX(x,y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
/* size와 할당 비트를 결합, header와 footer*/
/* 32        |   3 2 1 0             */
/* blocksize |     0 0 1 - allocated */
#define PACK(size, alloc) ((size) | (alloc))

/* p가 참조하는 워드 반환 */
#define GET(p) (*(unsigned int*)(p))

// p에 val 저장
#define PUT(p,val) (*(unsigned int*)(p) = (val))


// (0x7 = 0000_0111 -> ~0x7 = 1111_1000  '&' 연산으로 앞의 blocksize만 반환 )
#define GET_SIZE(p) (GET(p) & ~0x7)

// (0x1 = 0000_0001 '&' 연산으로 뒤의 allocated만 반환 )
#define GET_ALLOC(p) (GET(p) & 0x1)

/* 헤더의 포인터 */
#define HDRP(bp) ((char *)(bp) - WSIZE)

/* 푸터의 포인터 */
#define FTRP(bp) ((char *)(bp) +GET_SIZE(HDRP(bp)) - DSIZE)

/* 다음 블록의 포인터 */
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))

/* 이전 블록의 포인터 */
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))


#define PREC_FREEP(bp) (*(void**)(bp)) // 이전 블록의 bp에 들어있는 주소값을 리턴
#define SUCC_FREEP(bp) (*(void**)(bp + WSIZE)) // 이후 블록의 bp

//#define NEXT_FIT  // define하면 next_fit, 안 하면 first_fit으로 탐색
// Declaration
static void *heap_listp;
static void *free_listp;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

#ifdef NEXT_FIT
    static void* last_freep;  // next_fit 사용 시 마지막으로 탐색한 가용 블록
#endif

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* 메모리에서 6words를 가져오고 이걸로 빈 가용 리스트 초기화 */
    /* padding, prol_header, prol_footer, PREC, SUCC, epil_header */
    if ((heap_listp = mem_sbrk(6*WSIZE)) == (void*)-1)
        return -1;

    PUT(heap_listp, 0);  // Alignment padding. 더블 워드 경계로 정렬된 미사용 패딩.
    PUT(heap_listp + (1*WSIZE), PACK(2*DSIZE, 1));  // prologue header
    PUT(heap_listp + (2*WSIZE), NULL);  // prologue block안의 PREC 포인터 NULL로 초기화
    PUT(heap_listp + (3*WSIZE), NULL);  // prologue block안의 SUCC 포인터 NULL로 초기화
    PUT(heap_listp + (4*WSIZE), PACK(2*DSIZE, 1));  // prologue footer
    PUT(heap_listp + (5*WSIZE), PACK(0, 1));      // epliogue header

    free_listp = heap_listp + 2*WSIZE; // free_listp를 탐색의 시작점으로 둔다. 

    #ifdef NEXT_FIT
        last_freep = heap_listp;
    #endif

    /* 그 후 CHUNKSIZE만큼 힙을 확장해 초기 가용 블록을 생성한다. */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) //실패하면 -1 리턴
        return -1;

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{

    size_t asize;   /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhand and alignment reqs. */
    if (size <= DSIZE) // 8바이트 이하일 때  8의 배수를 맞춰주기 위해
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); // 8바이트 이상일 때 ex)size가 16일 때  8 * ((16 + 8 + 7 )) / 8 ) 8 * (31/8)으로 24 = 6word로 딱 맞게 된다.

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL){  // 
        place(bp,asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp,asize);
    return bp;
}


/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
    coalesce(bp);
}

static void* coalesce(void* bp){
    // 직전 블록의 footer, 직후 블록의 header를 보고 가용 여부를 확인.
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));  // 직전 블록 가용 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));  // 직후 블록 가용 여부
    size_t size = GET_SIZE(HDRP(bp));

    // case 1 : 직전, 직후 블록이 모두 할당 -> 해당 블록만 free list에 넣어주면 된다.

    // case 2 : 직전 블록 할당, 직후 블록 가용
    if(prev_alloc && !next_alloc){
        removeBlock(NEXT_BLKP(bp));    // free 상태였던 직후 블록을 free list에서 제거한다.
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // case 3 : 직전 블록 가용, 직후 블록 할당
    else if(!prev_alloc && next_alloc){
        removeBlock(PREV_BLKP(bp));    // 직전 블록을 free list에서 제거한다.
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp); 
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));  
    }

    // case 4 : 직전, 직후 블록 모두 가용
    else if (!prev_alloc && !next_alloc) {
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));  
        PUT(FTRP(bp), PACK(size, 0));  
    }

    // 연결된 새 가용 블록을 free list에 추가한다.
    putFreeBlock(bp);

    #ifdef NEXT_FIT
        last_freep = bp;
    #endif

    return bp;
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
    //copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
void putFreeBlock(void* bp){
    SUCC_FREEP(bp) = free_listp;
    PREC_FREEP(bp) = NULL;
    PREC_FREEP(free_listp) = bp;
    free_listp = bp;
}
void removeBlock(void *bp){
    // free list의 첫번째 블록을 없앨 때
    if (bp == free_listp){
        PREC_FREEP(SUCC_FREEP(bp)) = NULL;
        free_listp = SUCC_FREEP(bp);
    }
    // free list 안에서 없앨 때
    else{
        SUCC_FREEP(PREC_FREEP(bp)) = SUCC_FREEP(bp);
        PREC_FREEP(SUCC_FREEP(bp)) = PREC_FREEP(bp);
    }
}


static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words +1 ) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size,0));        /* Free block header */
    PUT(FTRP(bp), PACK(size,0));        /* Free block footer*/
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);    
}




static void* find_fit(size_t asize){
    /* First-fit */
    void* bp;

    // free list의 맨 뒤는 프롤로그 블록이다. Free list에서 유일하게 할당된 블록이므로 얘를 만나면 탐색 종료.
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC_FREEP(bp)){
        if(asize <= GET_SIZE(HDRP(bp))){
            return bp;
        }
    }

    // 못 찾으면 NULL을 리턴한다.
    return NULL;

}

static void place(void* bp, size_t asize){
    // 현재 할당할 수 있는 후보 가용 블록의 주소
    size_t csize = GET_SIZE(HDRP(bp));

    // 할당될 블록이므로 free list에서 없애준다.
    removeBlock(bp);

    // 분할이 가능한 경우
    if ((csize - asize) >= (2*DSIZE)){
        // 앞의 블록은 할당 블록으로
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        // 뒤의 블록은 가용 블록으로 분할한다.
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));

        // free list 첫번째에 분할된 블럭을 넣는다.
        putFreeBlock(bp);
    }
    else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}




