/* 
 * mm.c -  Simple allocator based on implicit free lists, 
 *         first fit placement, and boundary tag coalescing. 
 *
 * Each block has header and footer of the form:
 * 
 *      31                     3  2  1  0 
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      ----------------------------------- 
 * 
 * where s are the meaningful size bits and a/f is set 
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap  
 *  -----------------------------------------------------------------   
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 * 
 * The freelist is a linked list of free blocks. Each block has a header and 
 * a footer. It also has the adress of the previous and next blocks in the 
 * list.
 * begin                                                          end 
 * free block                                               free block   
 *  ---------------------------------------------------------------------------------       
 * | header (4) | prev block (8) | next block (8) | zero or more bytes | footer (4) | 
 *  ---------------------------------------------------------------------------------  
 * 
 * Each time a block is freed it is added to the front of the freelist. 
 * The blocks are coalesced when searching for a good fit (deferred coalescing)  
 */

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include "mm.h"
#include "memlib.h"
#include <stdint.h>

/* Your info */
team_t team = { 
    /* First and last name */
    "Preksha Patel",
    /* UID */
    "205173476", "Best Lab Ever!!"
}; 

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<16)  /* initial heap size (bytes) */
#define CHUNKSIZE1  (3<<16)
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(uint32_t *)(p))
#define PUT(p, val)  (*(uint32_t *)(p) = (val))  

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
/* $end mallocmacros */

/* Global variables */
static char *heap_listp;  /* pointer to first block */  
static void *freelist = NULL;  //list of free blocks

static void *extend_heap(size_t words);
static void placefront(void *bp, size_t asize);
static void *placeend(void *bp, size_t asize);  //places at end of free block
static void *find_fit(size_t asize);
static void *coalesce(void *bp, uint32_t* fsize);

static void remove_node (void * p);
static void add_node (void * p);

//Checker functions
static void findinlist(void * bp);
static void checklinkedlist();
void mm_checkheap(int verbose);
static void printblock(void *bp);
static void checkblock(void *bp);

static int cnt = 0; //to keep count 
/*           
 * mm_init - Initialize the memory manager    
 */
/* $begin mminit */
int mm_init(void)
{
  freelist = NULL;//initialize freelist to null
  if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL)
	return -1;
    PUT(heap_listp, 0);                        /* alignment padding */
    PUT(heap_listp+WSIZE, PACK(OVERHEAD, 1));  /* prologue header */ 
    PUT(heap_listp+DSIZE, PACK(OVERHEAD, 1));  /* prologue footer */
    
    PUT(heap_listp+WSIZE+DSIZE, PACK(0, 1));   /* epilogue header */
    heap_listp += DSIZE;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
	return -1;
    return 0;
}
/* $end mminit */
/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) 
{
  uint32_t asize;      /* adjusted block size */
  uint32_t extendsize; /* amount to extend heap if no fit */
  char *bp;
  
  /* Ignore spurious requests */
  if (size <= 0)
    return NULL;
  
  /* Adjust block size to include overhead and alignment reqs. */
  /*we make the minimum size 2*DSIZE+OVERHEAD to make it convinient for our implementation*/
  if (size <= DSIZE)
    asize = DSIZE*2 + OVERHEAD; 
  else
    asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);
  /* Search the free list for a fit */
  /* Alternate between placing the element at the end of the free block and at the start
     of the free block using the counter cnt by switch it between 1 and 0 */
  if ((bp = find_fit(asize)) != NULL) {
    if(cnt == 0) {
      cnt = 1; //flip the counter
      placefront(bp, asize); //places at the front of the free block
      return bp;
    }
    else {
      cnt = 0; //flip the counter
      return placeend(bp, asize); //places at end of free block
    }
  }  /* No fit found. Get more memory and place the block */

  extendsize = MAX(asize,CHUNKSIZE1);
  if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
    return NULL;
  placefront(bp, asize); //place it at the front of the free block
  
  return bp;
} 
/* $end mmmalloc */

/* 
 * mm_free - Free a block 
 */
/* $begin mmfree */
void mm_free(void *bp)
{
  uint32_t size = GET_SIZE(bp-WSIZE);
  PUT(bp-WSIZE, PACK(size, 0));
  PUT(bp+size-DSIZE, PACK(size, 0));  
  add_node(bp); //coalescing is deferred until later
}

/* $end mmfree */
/*
 * mm_realloc - naive implementation of mm_realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newp;
    size_t copySize;

    if ((newp = mm_malloc(size)) == NULL) {
	exit(1);
    }
    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize)
      copySize = size;
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}

/* 
 * mm_checkheap - Check the heap for consistency 
 */
void mm_checkheap(int verbose) 
{
  char *bp = heap_listp;

  if (verbose)
        printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
	printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
	if (verbose) 
	    printblock(bp);
	checkblock(bp);
	if (GET_ALLOC(HDRP(bp)) == 0)
	  {
	    findinlist(bp);
	  }
    }
     
    if (verbose)
	printblock(bp);

    checklinkedlist(); //this checks the linked list and if each node is valid
    
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
	printf("Bad epilogue header\n");

    
}

/* The remaining routines are internal helper routines */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) 
{
  char *bp;
  uint32_t size;
  
  /* Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
  if ((bp = mem_sbrk(size)) == (void *)-1) 
    return NULL;
  
  /* Initialize free block header/footer and the epilogue header */
  PUT(HDRP(bp), PACK(size, 0));         /* free block header */
  PUT(bp+size-DSIZE, PACK(size, 0));         /* free block footer */
  PUT(bp+size-WSIZE, PACK(0, 1)); /* new epilogue header */
  add_node(bp);
  return bp;
 
}
/* $end mmextendheap */

/* 
 * placefront - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplacefront */
static void placefront(void *bp, size_t asize) //This function places at the front of the freeblock
{
  
  uint32_t csize = GET_SIZE((char*)bp-WSIZE);   
  remove_node(bp); /*since we found bp from the free list we remove it from the free list*/
  uint32_t diff =csize - asize; /*this is the excess space we have left after allocating*/

  if (diff >= 24) { /*if the excess space is enough for allocating a free block*/
    PUT(bp-WSIZE, PACK(asize, 1));
    PUT(bp+asize-DSIZE, PACK(asize, 1));
    bp = bp+asize;
    PUT(bp-WSIZE, PACK(diff, 0));
    PUT(bp+diff-DSIZE, PACK(diff, 0));
    add_node(bp);
  }
  else { /*otherwise all the space is given to malloc*/
    PUT(bp-WSIZE, PACK(csize, 1));
    PUT(bp+csize-DSIZE, PACK(csize, 1));
  }
}
/* $end mmplacefront*/

/*                             
 * placeend - Place block of asize bytes at start of end block bp   
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplaceend*/
static void *placeend(void *bp, size_t asize)
{
  uint32_t csize = GET_SIZE((char*)bp-WSIZE);

  uint32_t diff =csize - asize;
  if (diff >= 24) {    /*if we have enough excess space to allocate a 
			 free block we leave the block in the free list*/
    PUT(bp-WSIZE, PACK(diff, 0));
    void * p = bp+diff;
    PUT(p-DSIZE, PACK(diff, 0));
    PUT(p-WSIZE, PACK(asize, 1));
    PUT(p+asize-DSIZE, PACK(asize, 1));
    return p;
  }
  else {  /* otherwise we remove the block from the freelist 
	     and give all the space to malloc*/
      remove_node(bp);
    PUT(bp-WSIZE, PACK(csize, 1));
    PUT(bp+csize-DSIZE, PACK(csize, 1));
    return bp;
  }  
}
/* $end mmplaceend */

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{
  void *p;
  uint32_t sizeb = 0;
  
  p = freelist;
  while( p != NULL) /*while there are elements in the free list, search for a fit*/
    {
      p = coalesce(p, &sizeb); /*we coalesce the block before checking it*/
      if (sizeb >= asize)/*if the fits are good enough, return it*/
        {
          return p;
        }
      p =*(void**)(p+DSIZE);
    }
  return NULL; /* no fit */
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
/*This implementation of coalesce has been made to work for deffered coalescing, allowing coalescing of multiple blocks on either sides */
static void* coalesce(void *bp, uint32_t* fsize)
{

  uint32_t size = GET_SIZE(HDRP(bp));
  uint32_t nsize, psize;
  char * start = bp - DSIZE;
  char * end = bp + size - WSIZE;

  uint32_t prev_alloc = GET_ALLOC(start);
  uint32_t next_alloc = GET_ALLOC(end);
  if (prev_alloc && next_alloc) {
    *fsize = size;
    return bp;
  }

  /*while the previous adjacent blocks are empty, remove those blocks from the linked list*/
  while (!prev_alloc)
    {
      psize = GET_SIZE(start);
      size += psize;
      start = start - psize;
      remove_node (start+DSIZE);
      prev_alloc = GET_ALLOC(start);
    }
  start += WSIZE;
  /*while the next adjacent blocks are empty remove those blocks from the linked list*/
  while (!next_alloc)
    {
      nsize = GET_SIZE(end);
      size += nsize;
      remove_node (end+WSIZE);
      end = end + nsize;
      next_alloc = GET_ALLOC(end);
    }
  end -= WSIZE;
  /*label the new block after coalescing*/
  PUT(start, PACK(size, 0));
  PUT(end, PACK(size, 0));
  start += WSIZE;
  /*add the new block to the linked list at the position where the original one was*/
  void * temp;
  if ((temp = *(void**)(bp)) != NULL)
    *(void**)(temp+8) = start;
  else
    freelist = start;
  if ((temp = *(void**)(bp+8)) != NULL)
    *(void**)(temp) = start;
  
  *(void**)(start) = *(void**)(bp);
  *(void**)(start+8) = *(void**)(bp+8);

  *fsize = size; /*set fsize to the new size of the block*/
  return start;

}

/*
 * remove_node - remove the node from the free list and 
 *               connect the previous and next node
 */
static void remove_node (void * p)
{
  void * prevb = *(void**) p;
  void * nextb = *(void**)(p+DSIZE);
 
  if (prevb == NULL) {
    freelist =nextb;
  }
  else {
    *(void**)(prevb+DSIZE)= nextb;
  }
  if (nextb != NULL) {
    *(void**)(nextb) = prevb;
  }
}

/* 
 * add_node - add a node to the beginning of the freelist
 */
static void add_node (void * p)
{
  if (freelist == NULL) {
    freelist = p;
    *(void**)(p) = NULL;
    *(void**)(p+DSIZE) = NULL;
  }
  else {
    *(void**)(p) = NULL;
    *(void**)(p+DSIZE) = freelist;
    *(void**)(freelist) = p;
    freelist = p;
  }
}



/*
 * checklinkedlist - check is all nodes in link list are actually
 *                  free blocks and if they are valid. Also check
 *                  for internal loops of the freelist.
 */
static void checklinkedlist()
{  
  uint32_t c, d;
  if (freelist == NULL)
    return;

  //to check if linked list has an internal loop which will result in infinitely many accesses
  void * p =*(void**)(freelist+8);
  void* q = freelist;
  while (p != q && p != NULL) {
    p = *(void**)(p+8);
    q = *(void**)(q+8);
    if (p ==NULL)
      return;
    p =	*(void**)(p+8);

  }
  if (p == q) {
    printf("Error: Linked list has a loop!\n");
    exit(1);
  }

  p = freelist;
  while (p != NULL) //check each element of the linked list
    {
      
      if ((c=GET_ALLOC(HDRP(p))) == 1){ //check if block is marked free in the header
	printf("Error: Header of block in freelist should be marked free\n");
	  exit(1);}
      if ((c=GET_ALLOC(FTRP(p))) == 1){ //check if block is marked free in the footer
        printf("Error: Footer of block in freelist should be marked free\n");
	  exit(1);}
      if ((c=GET_SIZE(FTRP(p))) != (d=GET_SIZE(HDRP(p)))){ //check if size is same in header and footer
	printf("Error: Size of the block mentioned in the front and the back should be the same\n Size in Header is %d    Size in Footer is %d\n",d, c);
	  exit(3);}
      if (c<24){ //check is size is atleast the minimum size of the block
	printf("Error: Size of block should be atleast 24");
	exit(4);
      }
      p = *(void**)(p+8);
    } 
}

/*
 * findinlist - checks if the all the free blocks are actually in 
 *             the freelist.
 */
static void findinlist(void * bp)
{
  void * a = freelist;
  while (a != NULL)
    {
      if (bp == a)
	return;
      a = *(void**)(a+8);
    }
  printf("Error: Free block not in free list\n");
}

/*
 * printblock - prints the block header and footer along with address.
 */
static void printblock(void *bp) 
{
    uint32_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  
    
    if (hsize == 0) {
        printf("%p: EOL\n", bp);
	return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, 
	   hsize, (halloc ? 'a' : 'f'), 
	   fsize, (falloc ? 'a' : 'f')); 
}

/*
 * checkblock - checks validity of the block
 */
static void checkblock(void *bp) 
{
    if ((uint32_t)bp % 8)
      printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
      printf("Error: header does not match footer\n");
}
