#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdlib.h>
#include <string.h>

typedef int64_t u64;

extern u64 our_code_starts_here() asm("our_code_starts_here");


// Print copied from lecture about function definitions.
const u64 BOOL_TAG   = 0x1;
const u64 BOOL_TRUE  = 0x3; // These must be the same values
const u64 BOOL_FALSE = BOOL_TAG; // as chosen in compile.ml

u64 print(u64 val) {
  if ((val & BOOL_TAG) == 0) { // val is even ==> number
    printf("> %ld\n", ((int64_t)(val)) / 2); // shift bits right to remove tag
  } else if (val & BOOL_TRUE) {
    printf("> true\n");
  } else if (val & BOOL_FALSE) {
    printf("> false\n");
  } else {
    printf("> %" PRId64 "\n", val); // print unknown val in hex
  }
  return val;
}

const u64 ERROR_NOT_BOOLEAN = 2LL;
const u64 ERROR_NOT_NUMBER = 1LL;

void typeError(u64 type, u64 givenValue) {
  if (type == ERROR_NOT_NUMBER)
    printf("Expected integer, but got %s.\n", (((givenValue & BOOL_TRUE) >> 1) ? "true" : "false"));
  else if (type == ERROR_NOT_BOOLEAN)
    printf("Expected boolean, but got %" PRId64 ".\n", givenValue >> 1);
  exit(type);
}

u64 safe = 1;
const u64 INT_MAX_OUR = 4611686018427387903;
const u64 INT_MIN_OUR = -4611686018427387904;

void check_overflow_add(u64 a1, u64 a2){
  if(safe){
    u64 real_a1 = a1 / 2;
    u64 real_a2 = a2 / 2;
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
    u64 real_a1 = a1 / 2;
    u64 real_a2 = a2 / 2;
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
    u64 real_a1 = a1 / 2;
    u64 real_a2 = a2 / 2;

    if((real_a1 == -1) && (real_a2 == INT_MIN_OUR)){
      printf("(* %" PRId64 " %" PRId64 ") will produce overflow.\n", real_a1, real_a2);
      exit(3);
    } else if((real_a2 == -1) && (real_a1 == INT_MIN_OUR)){
      printf("(* %" PRId64 " %" PRId64 ") will produce overflow.\n", real_a1, real_a2);
      exit(3);
    } else if(INT_MIN_OUR / real_a2 > real_a1){
      printf("(* %" PRId64 " %" PRId64 ") will produce underflow.\n", real_a1, real_a2);
      exit(4);
    } else if(INT_MAX_OUR / real_a2 < real_a1){
      printf("(* %" PRId64 " %" PRId64 ") will produce overflow.\n", real_a1, real_a2);
      exit(3);
    }
  }
}

void check_div_by_0(u64 a1){
  u64 real_a1 = a1 / 2;
  if(real_a1 == 0){
    printf("Division by 0\n");
    exit(5);
  }
}


int main(int argc, char** argv) {
  char* flag = "-safe";
  if(argc > 0){
    if(!strcmp(argv[0], flag)){
      safe = 1;
    }
  }
  u64 result = our_code_starts_here();

  u64 check = result & 1LL;
  result /= 2;
  if(check){
    if(result & 1LL){
      printf("true\n");
    } else {
      printf("false\n");
    }
  } else {
    printf("%" PRId64 "\n", result);
  }
  return 0;
}
