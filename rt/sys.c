#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

typedef uint64_t u64;

extern u64 our_code_starts_here() asm("our_code_starts_here");

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
