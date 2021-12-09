#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <sys/resource.h>

typedef int64_t u64;

/* configuration */
u64 STACK_SIZE = 0x800000;
u64 HEAP_SIZE = 16;
int USE_GC = 1;

/* externs */
extern void error(u64 err_code, u64 val) asm("error");
extern u64 print(u64 val) asm("print");
extern u64* try_gc(u64* alloc_ptr, u64 words_needed, u64* cur_frame, u64* cur_sp) asm("try_gc");
extern u64 our_code_starts_here(u64* heap) asm("our_code_starts_here");
extern void set_stack_bottom(u64* stack_bottom) asm("set_stack_bottom");
/* */

void print_value(u64 value);

// Print copied from lecture about function definitions.
const u64 NUM_TAG = 0x0;
const u64 TUP_TAG = 0x1;
const u64 BOOL_TAG = 0x2;
const u64 LBD_TAG = 0x3;
const u64 TYPE_MASK = 3LL;

// return 1 if value is a num, 0 otherwise
int is_num(u64 value){
  return (value & TYPE_MASK) == NUM_TAG;
}

// return 1 if value is a bool, 0 otherwise
int is_bool(u64 value){
  return (value & TYPE_MASK) == BOOL_TAG;
}

// return 1 if value is a tuple, 0 otherwise
int is_tuple(u64 value){
  return (value & TYPE_MASK) == TUP_TAG;
}

// return 1 if value is a lambda, 0 otherwise
int is_lbd(u64 value){
  return (value & TYPE_MASK) == LBD_TAG;
}


const u64 BOOL_TRUE  = 0x6; // These must be the same values
const u64 BOOL_FALSE = BOOL_TAG; // as chosen in compile.ml
const u64 ARITHMETIC_SHIFT_VAL = 4LL;
const u64 LOGICAL_SHIFT_VAL = 0x2;

// differents types of error
const u64 ERROR_WRONG_ARITY = 11LL;
const u64 ERROR_TUPLE_EMPTY = 10LL;
const u64 ERROR_INDEX_TOO_LOW = 9LL;
const u64 ERROR_INDEX_TOO_HIGH = 8LL;
const u64 ERROR_DIV_BY_0 = 7LL;
const u64 ERROR_UNDERFLOW = 6LL;
const u64 ERROR_OVERFLOW = 5LL;
const u64 ERROR_NOT_LAMBDA = 4LL;
const u64 ERROR_NOT_TUPLE = 3LL;
const u64 ERROR_NOT_BOOLEAN = 2LL;
const u64 ERROR_NOT_NUMBER = 1LL;

// print the type error
void typeError(u64 type, u64 givenValue) {
  if (type == ERROR_NOT_NUMBER)
    printf("Expected integer, but got ");
  else if (type == ERROR_NOT_BOOLEAN)
    printf("Expected boolean, but got ");
  else if (type == ERROR_NOT_TUPLE)
    printf("Expected tuple, but got ");
  else if (type == ERROR_NOT_LAMBDA)
    printf("Expected lambda, but got ");

  print_value(givenValue);
  printf(".\n");
  exit(type);
}

// print the index error
void indexError(u64 index, u64 sizeTuple) {
  if(sizeTuple == 0){
    printf("Tuple is empty, size tuple is 0.\n");
    exit(ERROR_TUPLE_EMPTY);
  } else if (index >= sizeTuple){
    printf("Index too high, maximum index is %" PRId64 ".\n", (sizeTuple / ARITHMETIC_SHIFT_VAL) - 1);
    exit(ERROR_INDEX_TOO_HIGH);
  } else {
    printf("Index too low, minimum index is 0.\n");
    exit(ERROR_INDEX_TOO_LOW);
  }
}

// print wrong arity
void wrongArity(u64 arity, u64 givenArity) {
  printf("Arity mismatch, expected %" PRId64 " arguments got %" PRId64 " arguments.\n", arity, givenArity);
  exit(ERROR_WRONG_ARITY);
}

// if safe is 1 check overflow, underflow and division by 0
// otherwise do nothing
u64 safe = 1;

// maximum values in our program of int
const u64 INT_MAX_OUR = 2305843009213693951;
const u64 INT_MIN_OUR = -2305843009213693952;

// print a value literally
void DEBUG(u64 a){
  printf("> DEBUG %" PRId64 "\n", a);
}

// check if add operation will overflow
void check_overflow_add(u64 a1, u64 a2){
  if(safe){
    u64 real_a1 = a1 / ARITHMETIC_SHIFT_VAL;
    u64 real_a2 = a2 / ARITHMETIC_SHIFT_VAL;
    if((real_a2 < 0) && (INT_MIN_OUR - real_a2 > real_a1)){
      printf("(+ %" PRId64 " %" PRId64 ") will produce underflow.\n", real_a1, real_a2);
      exit(ERROR_UNDERFLOW);
    } else if((real_a2 > 0) && (INT_MAX_OUR - real_a2 < real_a1)){
      printf("(+ %" PRId64 " %" PRId64 ") will produce overflow.\n", real_a1, real_a2);
      exit(ERROR_OVERFLOW);
    }
  }
}

// check if sub operation will overflow
void check_overflow_sub(u64 a1, u64 a2){
  if(safe){
    u64 real_a1 = a1 / ARITHMETIC_SHIFT_VAL;
    u64 real_a2 = a2 / ARITHMETIC_SHIFT_VAL;
    if((real_a2 > 0) && (INT_MIN_OUR + real_a2 > real_a1)){
      printf("(- %" PRId64 " %" PRId64 ") will produce underflow.\n", real_a1, real_a2);
      exit(ERROR_UNDERFLOW);
    } else if((real_a2 < 0) && (INT_MAX_OUR + real_a2 < real_a1)){
      printf("(- %" PRId64 " %" PRId64 ") will produce overflow.\n", real_a1, real_a2);
      exit(ERROR_OVERFLOW);
    }
  }
}

// check if mul operation will overflow
void check_overflow_mul(u64 a1, u64 a2){
  if(safe){
    u64 real_a1 = a1 / ARITHMETIC_SHIFT_VAL;
    u64 real_a2 = a2 / ARITHMETIC_SHIFT_VAL;

    if((real_a1 == -1) && (real_a2 == INT_MIN_OUR)){
      printf("(* %" PRId64 " %" PRId64 ") will produce overflow.\n", real_a1, real_a2);
      exit(ERROR_OVERFLOW);
    } else if((real_a2 == -1) && (real_a1 == INT_MIN_OUR)){
      printf("(* %" PRId64 " %" PRId64 ") will produce overflow.\n", real_a1, real_a2);
      exit(ERROR_OVERFLOW);
    } else if(real_a1 > 0 && real_a2 < 0 && INT_MIN_OUR / real_a2 < real_a1){
      printf("(* %" PRId64 " %" PRId64 ") will produce underflow.\n", real_a1, real_a2);
      exit(ERROR_UNDERFLOW);
    } else if(real_a1 > 0 && real_a2 > 0 && INT_MAX_OUR / real_a2 < real_a1){
      printf("(* %" PRId64 " %" PRId64 ") will produce overflow.\n", real_a1, real_a2);
      exit(ERROR_OVERFLOW);
    } else if(real_a1 < 0 && real_a2 < 0 && INT_MAX_OUR / (-1 * real_a2) < (-1 * real_a1)){
      printf("(* %" PRId64 " %" PRId64 ") will produce overflow.\n", real_a1, real_a2);
      exit(ERROR_OVERFLOW);
    } else if(real_a1 < 0 && real_a2 > 0 && INT_MIN_OUR / real_a2 > real_a1){
      printf("(* %" PRId64 " %" PRId64 ") will produce underflow.\n", real_a1, real_a2);
      exit(ERROR_UNDERFLOW);
    }
  }
}

// check if div operation will overflow
void check_div_by_0(u64 a1){
  u64 real_a1 = a1 / ARITHMETIC_SHIFT_VAL;
  if(real_a1 == 0){
    printf("Division by 0.\n");
    exit(ERROR_DIV_BY_0);
  }
}

// print a tuple
void print_tuple(u64 result){
  uint64_t* tuplePtr = (uint64_t*)(result - 1);
  u64 size = (*tuplePtr / ARITHMETIC_SHIFT_VAL);
  printf("(tup");
  for(u64 i = 1; i <= size; i++){
    printf(" ");
    u64 tupleI = *(tuplePtr + i);
    print_value(tupleI);
  }
  printf(")"); 
}

// print a value
void print_value(u64 value){
  if(is_num(value)) {
    value /= ARITHMETIC_SHIFT_VAL;
    printf("%" PRId64 "", value);
  } else if(is_bool(value)){
    value >>= LOGICAL_SHIFT_VAL;
    if(value & 1LL){
      printf("true");
    } else {
      printf("false");
    }
  } else if (is_tuple(value)) { // is tuple
    print_tuple(value);
  } else if (is_lbd(value)) {
    uint64_t* tuplePtr = (uint64_t*)(value - 3LL);
    printf("<clos:%" PRId64 ">", *tuplePtr);
  }
}

// do a print with > first
u64 print(u64 val) {
  printf("> ");
  print_value(val);
  printf("\n");
  return val;
}

/* GC */
u64* HEAP_START;
u64* HEAP_END;
u64* HEAP_MID;
u64* TO_SPACE;
u64* FROM_SPACE;
u64* ALLOC_PTR = 0;
u64* SCAN_PTR = 0;
u64* STACK_BOTTOM = 0;

void set_stack_bottom(u64* stack_bottom) {
  STACK_BOTTOM = stack_bottom;
}

bool is_heap_ptr(u64 val){
  return (u64*)val < HEAP_END && (u64*)val >= HEAP_START;
}

void print_stack(u64* rbp, u64* rsp) {
  printf("|------- frame %p to %p  ------\n", rsp, rbp);
  for (u64* cur_word = rsp; cur_word < rbp; cur_word++) {
    u64 val = (u64)*cur_word;
    printf("| %p: %p", cur_word, (u64*)*cur_word);
    if (is_heap_ptr(val)) {
      if (is_tuple(val)){ printf(" (tuple)"); }
      else if (is_lbd(val)){ printf(" (closure)"); }
    }
    printf("\n");
  }
  if (rbp < STACK_BOTTOM) {
    print_stack((u64*)*rbp, rbp + 2);
  }
  else {
    printf("|------- bottom %p  ------\n\n", STACK_BOTTOM);
  }
}

void print_heap(u64* heap_start, u64* heap_end){
  printf("| Heap from %p to %p\n", heap_start, heap_end);
  for (u64 i = 0; i <= (u64)(heap_end - heap_start); i++) {
    printf("|  %ld/%p: %p \n", i, (heap_start + i), (u64*)*(heap_start + i));
  }
}

void print_heaps(){
  char* to_print = (HEAP_START == FROM_SPACE ? "FROM_SPACE" : "TO_SPACE");
  printf("|\n|=======HEAP 1 %s==========\n", to_print);
  print_heap(HEAP_START, HEAP_MID-1);
  printf("|=======HEAP 2 %s==========\n", (HEAP_MID == FROM_SPACE ? "FROM_SPACE" : "TO_SPACE"));
  print_heap(HEAP_MID, HEAP_END);
  printf("|=================\n\n");
}

// do swap of pointer for two pointers
void swap(u64** a, u64** b){
  u64* aux = *a;
  *a = *b;
  *b = aux;
}

// for a given pointer return the size to copy
u64 size_of_ptr(u64* o, u64 tag){
  if (is_tuple(tag)) { // is tuple

    u64 size = (*o / ARITHMETIC_SHIFT_VAL);
    return size + 1;
  
  } else if (is_lbd(tag)) {
  
    u64 freeVars = *(o + 2);
    return freeVars + 3;
  
  }
  return -1;
}

// copy from one heap to another
u64* copy(u64* o, u64 tag){
  u64* new_o = ALLOC_PTR;
  u64 size_o = size_of_ptr(o, tag);

  ALLOC_PTR = ALLOC_PTR + size_o;

  for(u64 i = 0; i < size_o; i++){
    *(new_o + i) = *(o + i);
  }

  return new_o;
}

// do collect follow Cheney's algorithm
u64* collect(u64* cur_frame, u64* cur_sp) {
  /* TBD: see https://en.wikipedia.org/wiki/Cheney%27s_algorithm */
  // swap from-space to-space
  swap(&FROM_SPACE, &TO_SPACE);
  // init spaces
  ALLOC_PTR = TO_SPACE;
  SCAN_PTR = TO_SPACE;
  // scan stack and copy roots
  for (u64* root = cur_sp; root < cur_frame; root++) {
    u64 tag_root = (((u64)*root) & 3LL);
    u64* root_no_tag = (u64*)(((u64)*root) - tag_root);
    if(is_heap_ptr((u64)root_no_tag) && (!is_num(tag_root)) && (!is_bool(tag_root))){
      *root = ((u64)copy(root_no_tag, tag_root)) + tag_root;
    }
  }
  // scan objects in the heap
  while(SCAN_PTR < ALLOC_PTR){
    u64 tag_scan = (((u64)*SCAN_PTR) & 3LL);
    u64* scan_no_tag = (u64*)(((u64)*SCAN_PTR) - tag_scan);
    if(is_heap_ptr((u64)scan_no_tag) && (!is_num(tag_scan)) && (!is_bool(tag_scan))){
      *SCAN_PTR = ((u64)copy(scan_no_tag, tag_scan)) + tag_scan;
    }
    SCAN_PTR++;
  }
  // clean old space
  for(u64* i = FROM_SPACE; i < FROM_SPACE + HEAP_SIZE; i++){
    *i = 0x0;
  }
  return ALLOC_PTR;
}

// check if the from space is clean
// if is not cleaned will produce an error
void check_cleaned_from_space(){
  for(u64* i = FROM_SPACE; i < FROM_SPACE + HEAP_SIZE; i++){
    if(*i != 0x0){
      printf("| FROM_SPACE NOT CLEANED CORRECTLY\n");
      exit(245003);
    }
  }
}

/* trigger GC if enabled and needed, out-of-memory error if insufficient */
u64* try_gc(u64* alloc_ptr, u64 words_needed, u64* cur_frame, u64* cur_sp) {
  if (USE_GC==1 && alloc_ptr + words_needed > TO_SPACE + HEAP_SIZE) {
    printf("| need memory: GC!\n");
    alloc_ptr = collect(cur_frame, cur_sp);
    check_cleaned_from_space();
  }
  if (alloc_ptr + words_needed > TO_SPACE + HEAP_SIZE) {
    printf("| Error: out of memory!\n\n");
    print_stack(cur_frame, cur_sp);
    print_heaps();
    exit(-1);
  }
  return alloc_ptr;
}

// return if we are using GC or not
u64 getUseGC(){
  return USE_GC;
}

int main(int argc, char** argv) {
  /* stack size config */
  char* stack_size_envvar = getenv("STACK_SIZE");
  if (stack_size_envvar)
    STACK_SIZE = strtoull(stack_size_envvar, NULL, 0);
  printf("| Setting stack size to %" PRId64 " .\n", STACK_SIZE);
  
  struct rlimit limit;
  getrlimit(RLIMIT_STACK, &limit);
  limit.rlim_cur = STACK_SIZE < limit.rlim_max ? STACK_SIZE : limit.rlim_max;
  int res = setrlimit(RLIMIT_STACK, &limit);
  if (res != 0) { printf("| Setting rlimit failed...\n") ; }

  /* GC config */
  char* use_gc_envvar = getenv("USE_GC");
  if (use_gc_envvar) 
    USE_GC = strtoull(use_gc_envvar, NULL, 0);
  printf("| Use GC: %d\n", USE_GC);
  
  /* heap size config */
  char* heap_size_envvar = getenv("HEAP_SIZE");
  if (heap_size_envvar) 
    HEAP_SIZE = strtoull(heap_size_envvar, NULL, 0);
  printf("| Heap size: %" PRId64 " .\n", HEAP_SIZE);
  
  /* setting up two space heap for GC */
  u64* heap = (u64*)calloc((HEAP_SIZE * 2) + 7, sizeof(u64));
  HEAP_START = (u64*)(((u64)heap + 7) & 0xfffffffffffffff8);
  /* TBD: initialize HEAP_MID, HEAP_END, FROM_SPACE, TO_SPACE */
  HEAP_MID = (u64*)((((u64)heap + (HEAP_SIZE * 8)) + 7) & 0xfffffffffffffff8);   /* TBD */
  HEAP_END = (u64*)((((u64)heap + ((HEAP_SIZE * 8) * 2 - 8)) + 7) & 0xfffffffffffffff8);;   /* TBD */
  FROM_SPACE = HEAP_MID; /* TBD */
  TO_SPACE = HEAP_START;   /* TBD */

  /* Go! */
  /* Q: when do you need to call `free(heap)`? */

  u64 result = our_code_starts_here(HEAP_START);
  print_value(result);
  printf("\n");
  free(heap);
  return 0;
}
