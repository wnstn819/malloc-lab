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
#define CHUNKSIZE   (1<<) /* 한 확장을 위한 기본 크기 */


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

#define NEXT_FIT  // define하면 next_fit, 안 하면 first_fit으로 탐색
// Declaration
static void *heap_listp;
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

    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1)
        return -1;
    PUT(heap_listp,0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0,1));     /* Epilogue header */
    heap_listp += (2*WSIZE);

    #ifdef NEXT_FIT
        last_freep = heap_listp;
    #endif

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
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
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL){
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

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc){ /* Case 1 */
        return bp;
    }
    else if( prev_alloc && !next_alloc){ /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));

    }
    else if(!prev_alloc && next_alloc){ /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    else{                               /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }

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




static void *find_fit(size_t asize){
/* Next-fit */
    #ifdef NEXT_FIT
        void* bp;
        void* old_last_freep = last_freep;

        // 이전 탐색이 종료된 시점에서부터 다시 시작한다.
        for (bp = last_freep; GET_SIZE(HDRP(bp)); bp = NEXT_BLKP(bp)){
            if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
                return bp;
        }

        /*
        만약 끝까지 찾았는데도 안 나왔으면 처음부터 찾아본다.
        이 구문이 없으면 바로 extend_heap을 하는데, 
        이럼 앞에 있는 가용 블록들을 사용하지 못할 수 있어 메모리 낭비이다.
        */
        for (bp = heap_listp; bp < old_last_freep; bp = NEXT_BLKP(bp)){
            if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
                return bp;
        }

        last_freep = bp;  // 다시 탐색을 마친 시점으로 last_freep를 돌린다.

        return NULL;

		/* first-fit */
    #else
        void* bp;

        // 프롤로그 블록에서 에필로그 블록 전까지 블록 포인터 bp를 탐색한다.
        // 블록이 가용 상태이고 사이즈가 요구 사이즈보다 크다면 해당 블록 포인터를 리턴
        for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
            if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
                return bp;
            }
        }

        // 못 찾으면 NULL을 리턴한다.
        return NULL;
    #endif

    // void *bp;

    // for(bp= heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
    //     if ( !GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
    //         return bp;

    //     }
    // }
    // return NULL;
}

static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기

    if((csize - asize) >= (2 * DSIZE)){ // 현재 블록에는 필요한 만큼만 할당
        PUT(HDRP(bp),PACK(asize,1));
        PUT(FTRP(bp),PACK(asize,1));
        
        PUT(HDRP(NEXT_BLKP(bp)), PACK((csize-asize),0)); //남은 크기를 다음 블록에 할당(가용 블록)
        PUT(FTRP(NEXT_BLKP(bp)),PACK((csize-asize),0));

    }else{
        PUT(HDRP(bp),PACK(csize,1));
        PUT(FTRP(bp),PACK(csize,1));
    }

}




