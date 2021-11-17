#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdlib.h>
#include <string.h>

typedef int64_t u64;

extern u64 our_code_starts_here() asm("our_code_starts_here");

void print_value(u64 value);

// Print copied from lecture about function definitions.
const u64 NUM_TAG = 0x0;
const u64 TUP_TAG = 0x1;
const u64 BOOL_TAG = 0x2;
const u64 LBD_TAG = 0x3;

const u64 BOOL_TRUE  = 0x6; // These must be the same values
const u64 BOOL_FALSE = BOOL_TAG; // as chosen in compile.ml
const u64 ARITHMETIC_SHIFT_VAL = 4LL;
const u64 LOGICAL_SHIFT_VAL = 0x2;

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

void typeError(u64 type, u64 givenValue) {
  if (type == ERROR_NOT_NUMBER)
    printf("Expected integer, but got ");
  else if (type == ERROR_NOT_BOOLEAN)
    printf("Expected boolean, but got ");
  else
    printf("Expected tuple, but got ");

  print_value(givenValue);
  printf(".\n");
  exit(type);
}

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

void wrongArity(u64 arity, u64 givenArity) {
  printf("Arity mismatch, expected %" PRId64 " arguments got %" PRId64 " arguments.\n", arity, givenArity);
  exit(ERROR_WRONG_ARITY);
}

u64 safe = 1;
const u64 INT_MAX_OUR = 2305843009213693951;
const u64 INT_MIN_OUR = -2305843009213693952;

void DEBUG(u64 a){
  printf("> DEBUG %" PRId64 "\n", a);
}

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

void check_div_by_0(u64 a1){
  u64 real_a1 = a1 / ARITHMETIC_SHIFT_VAL;
  if(real_a1 == 0){
    printf("Division by 0.\n");
    exit(ERROR_DIV_BY_0);
  }
}

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

void print_value(u64 value){
  if(NUM_TAG == (value & 3LL)) {
    value /= ARITHMETIC_SHIFT_VAL;
    printf("%" PRId64 "", value);
  } else if(BOOL_TAG == (value & 3LL)){
    value >>= LOGICAL_SHIFT_VAL;
    if(value & 1LL){
      printf("true");
    } else {
      printf("false");
    }
  } else if (TUP_TAG == (value & 3LL)) { // is tuple
    print_tuple(value);
  } else if (LBD_TAG == (value & 3LL)) {
    uint64_t* tuplePtr = (uint64_t*)(value - 3LL);
    printf("<clos:%" PRId64 ">", *tuplePtr);
  }
}

u64 print(u64 val) {
  printf("> ");
  print_value(val);
  printf("\n");
  return val;
}

int main(int argc, char** argv) {
  char* flag = "-safe";
  if(argc > 0){
    if(!strcmp(argv[0], flag)){
      safe = 1;
    }
  }
  uint64_t *heap = calloc(1024, sizeof(uint64_t));

  u64 result = our_code_starts_here(heap);
  print_value(result);
  printf("\n");
  free(heap);
  return 0;
}
