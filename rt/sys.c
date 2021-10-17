#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

typedef int64_t u64;

extern u64 our_code_starts_here() asm("our_code_starts_here");

int main(int argc, char** argv) {
  u64 result = our_code_starts_here();

  u64 check = result & 1LL;
  if(check){
    result >>= 1;
    if(result & 1LL){
      printf("true\n");
    } else {
      printf("false\n");
    }
  } else {
    result /= 2;
    printf("%" PRId64 "\n", result);
  }
  return 0;
}
