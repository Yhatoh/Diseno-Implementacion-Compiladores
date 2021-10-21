#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdlib.h>
#include <string.h>

typedef int64_t u64;

extern u64 our_code_starts_here() asm("our_code_starts_here");

void print_value(u64 value);

// Print copied from lecture about function definitions.
const u64 BOOL_TAG   = 0x2;
const u64 BOOL_TRUE  = 0x6; // These must be the same values
const u64 BOOL_FALSE = BOOL_TAG; // as chosen in compile.ml
const u64 ARITHMETIC_SHIFT_VAL = 0x4;
const u64 LOGICAL_SHIFT_VAL = 0x2;

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
  printf("\n");
  exit(type);
}

void indexError(u64 index, u64 sizeTuple) {
  if(sizeTuple == 0){
    printf("Tuple is empty, size tuple is 0\n");
    exit(8);
  } else if (index >= sizeTuple){
    printf("Index too high, maximum index is %" PRId64 ".\n", (sizeTuple / ARITHMETIC_SHIFT_VAL) - 1);
    exit(7);
  } else {
    printf("Index too low, minimum index is 0.\n");
    exit(6);
  }
}

u64 safe = 1;
const u64 INT_MAX_OUR = 4611686018427387903 / 2;
const u64 INT_MIN_OUR = -4611686018427387904 / 2;

void check_overflow_add(u64 a1, u64 a2){
  if(safe){
    u64 real_a1 = a1 / ARITHMETIC_SHIFT_VAL;
    u64 real_a2 = a2 / ARITHMETIC_SHIFT_VAL;
    if((real_a2 < 0) && (INT_MIN_OUR - real_a2 > real_a1)){
      printf("(+ %" PRId64 " %" PRId64 ") will produce underflow.\n", real_a1, real_a2);
      exit(4);
    } else if((real_a2 > 0) && (INT_MAX_OUR - real_a2 < real_a1)){
      printf("(+ %" PRId64 " %" PRId64 ") will produce overflow.\n", real_a1, real_a2);
      exit(3);
    }
  }
}

void check_overflow_sub(u64 a1, u64 a2){
  if(safe){
    u64 real_a1 = a1 / ARITHMETIC_SHIFT_VAL;
    u64 real_a2 = a2 / ARITHMETIC_SHIFT_VAL;
    if((real_a2 > 0) && (INT_MIN_OUR + real_a2 > real_a1)){
      printf("(- %" PRId64 " %" PRId64 ") will produce underflow.\n", real_a1, real_a2);
      exit(4);
    } else if((real_a2 < 0) && (INT_MAX_OUR + real_a2 < real_a1)){
      printf("(- %" PRId64 " %" PRId64 ") will produce overflow.\n", real_a1, real_a2);
      exit(3);
    }
  }
}

void check_overflow_mul(u64 a1, u64 a2){
  if(safe){
    u64 real_a1 = a1 / ARITHMETIC_SHIFT_VAL;
    u64 real_a2 = a2 / ARITHMETIC_SHIFT_VAL;

    if((real_a1 == -1) && (real_a2 == INT_MIN_OUR)){
      printf("(* %" PRId64 " %" PRId64 ") will produce overflow.\n", real_a1, real_a2);
      exit(3);
    } else if((real_a2 == -1) && (real_a1 == INT_MIN_OUR)){
      printf("(* %" PRId64 " %" PRId64 ") will produce overflow.\n", real_a1, real_a2);
      exit(3);
    } else if(real_a1 > 0 && real_a2 < 0 && INT_MIN_OUR / real_a2 < real_a1){
      printf("(* %" PRId64 " %" PRId64 ") will produce underflow.\n", real_a1, real_a2);
      exit(4);
    } else if(real_a1 > 0 && real_a2 > 0 && INT_MAX_OUR / real_a2 < real_a1){
      printf("(* %" PRId64 " %" PRId64 ") will produce overflow.\n", real_a1, real_a2);
      exit(3);
    } else if(real_a1 < 0 && real_a2 < 0 && INT_MAX_OUR / (-1 * real_a2) < (-1 * real_a1)){
      printf("(* %" PRId64 " %" PRId64 ") will produce overflow.\n", real_a1, real_a2);
      exit(3);
    } else if(real_a1 < 0 && real_a2 > 0 && INT_MIN_OUR / real_a2 > real_a1){
      printf("(* %" PRId64 " %" PRId64 ") will produce underflow.\n", real_a1, real_a2);
      exit(4);
    }
  }
}

void check_div_by_0(u64 a1){
  u64 real_a1 = a1 / ARITHMETIC_SHIFT_VAL;
  if(real_a1 == 0){
    printf("Division by 0\n");
    exit(5);
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
    /*
    u64 check = tupleI & 2LL;
    if(check){
      tupleI >>= LOGICAL_SHIFT_VAL;
      if(tupleI & 1LL){
        printf("true");
      } else {
        printf("false");
      }
    } else if (tupleI & 1LL) { // is tuple
      print_tuple(tupleI);
    } else {
      tupleI /= ARITHMETIC_SHIFT_VAL;
      printf("%" PRId64 "", tupleI);
    }
    */
  }
  printf(")"); 
}

void print_value(u64 value){
  u64 check = value & 2LL;
  if(check){
    value >>= LOGICAL_SHIFT_VAL;
    if(value & 1LL){
      printf("true");
    } else {
      printf("false");
    }
  } else if (value & 1LL) { // is tuple
    print_tuple(value);
  } else {
    value /= ARITHMETIC_SHIFT_VAL;
    printf("%" PRId64 "", value);
  }
}

u64 print(u64 val) {
  //printf("> DEBUG %" PRId64 "\n", val);
  printf("> ");
  print_value(val);
  printf("\n");
  /*
  if ((val & BOOL_TAG) == 0) { // val is even ==> number
    if(val & 1LL){
      printf("> ");
      print_tuple(val);
      printf("\n");
    } else { 
      printf("> %ld\n", ((int64_t)(val)) / ARITHMETIC_SHIFT_VAL); // shift bits right to remove tag
    }
  } else if ((val & BOOL_TRUE) / ARITHMETIC_SHIFT_VAL) {
    printf("> true\n");
  } else if ((val & BOOL_FALSE)) {
    printf("> false\n");
  } else {
    printf("> %" PRId64 "\n", val); // print unknown val in hex
  }
  */
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
  /*
  u64 check = result & 2LL;
  if(check){
    result >>= LOGICAL_SHIFT_VAL;
    if(result & 1LL){
      printf("true\n");
    } else {
      printf("false\n");
    }
  } else if (result & 1LL) { // is tuple
    print_tuple(result);
    printf("\n");
  } else {
    result /= ARITHMETIC_SHIFT_VAL;
    printf("%" PRId64 "\n", result);
  }
  */
  free(heap);
  return 0;
}
