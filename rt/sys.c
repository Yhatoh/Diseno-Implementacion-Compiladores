#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdlib.h>

typedef uint64_t u64;

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


int main(int argc, char** argv) {
  u64 result = our_code_starts_here();

  u64 check = result & 1LL;
  result >>= 1;
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
