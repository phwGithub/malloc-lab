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
#include <unistd.h> // unistd.h 헤더파일은 리눅스에는 있는 헤더지만 윈도우에는 없어서 오류가 뜬다. 어차피 서버에서 디버깅하니 신경 쓸 필요가 없다.
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "4 Team",
    /* First member's full name */
    "JO MIN",
    /* First member's email address */
    "cyun0717@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

// 혹시 몰라서 남겨놈
// /* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
// /* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// 가용 리스트 조작을 위한 기본 상수와 매크로 ------------------------------------------------------------------------------------------------

// --- 기본 size 상수 (bp = 블록 포인터) ---

#define WSIZE 4 // 워드의 크기

#define DSIZE 8 // 더블 워드의 크기

#define CHUNKSIZE (1<<12) // 초기 가용 블록과 힙 확장을 위한 기본 크기 (2의 12승 = 4kb)

#define MAX(x,y) ((x) > (y)? (x) : (y)) // 이건 어따 쓰는지 모르것네....

// --- 가용 리스트에 접근하고 방문하는 매크로들 ---

#define PACK(size, alloc) ((size) | (alloc)) // 크기와 할당 비트를 통합해서 헤더와 풋터안에 들어가는 값 리턴

#define GET(p) (*(unsigned int*)(p)) // 인자 p가 참조라는 워드를 리턴
// p인자는 (void*)형 포인터이다. 이것은 직접적으로 역참조 할 수 없다.

#define PUT(p, val) (GET(p) = (val)) // 인자 p가 가리키는 워드(주소)에 val을 저장한다.

#define GET_SIZE(p)  (GET(p) & ~0x7) // 주소 p에 있는 헤더 또는 풋터에 있는 블록 size리턴 / ~0x7 = 1111....(29비트)000

#define GET_ALLOC(p) (GET(p) & 0x1) // 주소 p에 있는 헤더 또는 풋터에 있는 블록 할당 비트 리턴 / 0x1 = 000...(29비트)001

#define HDRP(bp) ((char *)(bp) - WSIZE) // 블록의 헤더를 가리키는 포인터 리턴 / 블록 시작점(bp, 헤더 끝지점)에서 - 1워드 하면 헤더의 시작점이다.

#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 블록의 풋터를 가리키는 포인터 리턴 
// 블록 시작점에 해당 블록 사이즈(헤더 풋터 포함)을 더해주면 -> bp + 해당 블록의 총크기 - DSIZE하면 풋터의 시작점이 나온다.

#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp))) // 다음 블록의 블록 포인터를 리턴 / 해당 블록 포인터 + 해당 블록의 사이즈

#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 해당 블록 이전 블록의 블록 포인터를 리턴 / 해당 블록 포인터 - 이전 블록의 사이즈

static char* heap_listp;

// coalesce 함수 -------------------------------------------------------------------------------------------------------------

// 해당 블록 인접 가용 블록이 있다면 하나의 큰 블록으로 연결해주는 함수
static void* coalesce(void *bp){

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록이 할당 되었는지
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록이 할당 되었는지
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 사이즈

    // Case 1 : 이전과 다음 블록이 모두 할당 되었을 경우
    if (prev_alloc && next_alloc)
        return bp;
    // Case 2 : 이전 블록은 할당 상태, 다음 블록은 가용 상태일 경우
    else if (prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 사이즈에 다음 블록 사이즈를 더해준다.
        PUT(HDRP(bp), PACK(size, 0)); // 새로운 사이즈로 헤더 설정
        PUT(FTRP(bp), PACK(size, 0)); // 다음 블록의 풋터를 새로운 사이즈로 새로운 풋터 설정
    }
    // Case 3 : 이전 블록은 가용 상태, 다음 블록은 할당 상태일 경우
    else if (!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // 사이즈에 이전 블록 사이즈를 더해준다.
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 헤더에 새로운 사이즈로 새로운 헤더 설정
        PUT(FTRP(bp), PACK(size, 0)); // 해당 블록의 풋터에 새로운 사이즈로 새로운 풋터 설정
        bp = PREV_BLKP(bp); // bp을 이전 블록의 bp값으로 설정
    }
    // Case 4 : 이전, 다음 블록 모두 가용 상태일 경우
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 사이즈에 이전,다음 블록의 사이즈를 더해준다.
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 헤더에 새로운 사이즈로 헤더 설정
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록의 풋터에 새로운 사이즈로 풋터 설정
        bp = PREV_BLKP(bp); // bp을 이전 블록의 bp값으로 설정
    }
    return bp; // 새로운 bp을 리턴

}

// extend_heap 함수 -----------------------------------------------------------------------------------------------------------

// 힙의 영역을 늘려주는 함수
/*
    두 가지 경우에 호출된다.
    1. 힙이 초기화 될 때
    2. mm_malloc이 적당한 맞춤을 찾지 못했을경우
*/
static void* extend_heap(size_t words){ // 매개변수로 워드의 개수를 받는다.
 
    char* bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 블록의 크기를 8의 배수로 주기 위해 size를 2의 배수로 정한다.
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    // mem_sbrk함수는 성공시 이전 brk를 리턴하고 실패시 -1을 리턴

    PUT(HDRP(bp), PACK(size, 0)); // mem_sbrk에서 만든 새로운 블록의 헤더설정
    PUT(FTRP(bp), PACK(size, 0)); // 새로운 블록의 풋터 설정
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); // 메모리가 늘어 났으니깐 에필로그 재설정

    return coalesce(bp); // 앞에 빈 블록이 있을수 있으니 통합 하기위해 함수 호출

}

// mm_init 함수 ---------------------------------------------------------------------------------------------------------------

// 힙을 초기화 한다. 
int mm_init(void){
                                
    if ((heap_listp = mem_sbrk(WSIZE * 4)) == (void*)-1) // 메모리 시스템에서 4워드를 가져와 빈 가용 리스트를 만든다.
    return -1;                                         
    // sbrk함수는 실패시 (void*)-1을 리턴한다 성공시 이전 brk을 리턴 
    
    PUT(heap_listp, 0); // 미사용 패딩 워드
    PUT(heap_listp + (WSIZE * 1), PACK(DSIZE, 1)); // 프롤로그 헤더 / 할당 상태로 선언
    PUT(heap_listp + (WSIZE * 2), PACK(DSIZE, 1)); // 프롤로그 풋터 / 마찬가지로 할당 상태로 선언
    PUT(heap_listp + (WSIZE * 3), PACK(0,1)); // 에필로그 / 크기는 0, 상태는 할당 상태로
    heap_listp += (WSIZE * 2); // 프롤로그 헤더와 풋터사이로 이동

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) // 
        return -1;
    return 0;
}

// place 함수 ----------------------------------------------------------------------------------------------------------------

// 블록을 할당하고 남는 부분을 가용 블록으로 분할해준다.
static void place(void *bp, size_t asize){

    size_t block_size = GET_SIZE(HDRP(bp)); // bp가 가르키는 블록의 크기
    size_t rest_size = block_size - asize;  // 블록의 남는 부분의 크기

    // block_size에서 asize만큼 할당해주고 남는 부분이 최소 블록 크기 보다 클 경우
    if (rest_size >= DSIZE * 2){
        // asize만큼의 블록의 헤더와 풋터 설정
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp); // bp에 남는 블록의 bp값으로 설정
        // rest_size만큼의 블록의 헤더와 풋터 설정
        PUT(HDRP(bp), PACK(rest_size, 0));
        PUT(FTRP(bp), PACK(rest_size, 0));
    }
    // 남는 부분이 최소 블럭 크기 보다 작을 경우
    else{
        PUT(HDRP(bp), PACK(block_size, 1));
        PUT(FTRP(bp), PACK(block_size, 1));
    }
}

// find_fit 함수 ------------------------------------------------------------------------------------------------------------

// 요청 받은 블록의 크기가 들어갈 블록이 힙 영역에 있는 찾는다.
static void* find_fit(size_t asize){

    void *bp;
/*
    bp을 이용하여 힙영역의 블록들의 크기를 확인한다. 
    size가 0인 블록(에필로그 블록)이 나올때 까지. 
    bp는 다음 블록의 bp로 갱신하면서 간다.*/
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            // 할당 되지 않은 블록 이면서 asize보다 같거나 큰 사이즈의 블록을 찾은 경우
            return bp;
    }
    // 맞는 블록을 찾지 못한 경우
    return NULL;
}

// mm_malloc 함수 ------------------------------------------------------------------------------------------------------------

// size바이트의 메모리 블록을 요청하면 size바이트에 알맞는 메모리를 할당해준다.

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    // 요청 size가 0인 경우
    if (size == 0)
        return NULL;

    // 실제 할당 받아야 할 블록 사이즈 계산(8의 배수로 할당해 주어야하기에)(헤더와 풋터의 공간까지)
    if (size <= DSIZE) // 최소 블록 사이즈보다 작을 경우
        asize = DSIZE * 2;
    else
        asize = DSIZE * ((size + (DSIZE * 2) - 1) / DSIZE);
    
    // find_fit함수를 사용하여 할당 가능한 블록 찾기, 있으면 할당
    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize); // 남은 부분이 있을수 있으니 분할 함수 호출
        return bp;
    }

    // 요청한 size에 맞는 할당 가능 블록이 없다면
    extendsize = MAX(asize, CHUNKSIZE); // 힙 영역에 새로운 가용 블록의 크기를 asize랑 CHUNKSIZE중 큰 값으로 설정
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) // bp에 새로운 가용 블록의 bp를 담는다
        return NULL; // 만일 힙을 연장 할 수 없다면 NULL 리턴
    place(bp, asize); // 남는 부분을 분할
    return bp;
}

// mm_free 함수 --------------------------------------------------------------------------------------------------------

// 할당 받은 블록을 반납
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); // 반납할 블록의 크기를 알아온다.

    PUT(HDRP(bp), PACK(size, 0)); // 반납할 블록의 헤더의 할당 비트를 수정
    PUT(FTRP(bp), PACK(size, 0)); // 풋터도 수정
    coalesce(bp); // 반납 이후 연결해야 할 상황이 올수도 있으니 연결 함수 호출

}

// mm_realloc 함수 -----------------------------------------------------------------------------------------------------

// 크기를 조정할 블록의 위치와 요청 사이즈를 받아 해당 블록의 사이즈를 변경해준다.
void *mm_realloc(void *bp, size_t size)
{
    // 요청 받은 사이즈가 0보다 같거나 작으면 free시킨다.
    if (size <= 0){
        mm_free(bp);
        return 0;
    }

    // bp가 가르키는 블록이 NULL이면 새 블록을 할당해준다.
    if (bp == NULL)
        return mm_malloc(size);
    
    // 요청한 사이즈의 블록을 새로 할당 받는다.
    void *newp = mm_malloc(size);
    if (newp == NULL)
        return 0;
    
    // 요청 사이즈가 기존 사이즈보다 작으면 요청 사이즈만큼의 데이터만 잘라서 옮겨준다.
    size_t oldsize = GET_SIZE(HDRP(bp));
    if (size < oldsize)
        oldsize = size;
    memcpy(newp, bp, oldsize);
    mm_free(bp);
    return newp;
}