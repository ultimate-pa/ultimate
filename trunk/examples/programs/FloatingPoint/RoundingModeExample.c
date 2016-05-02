#include <math.h>
#include <stdio.h>
#include <fenv.h>
#include <float.h>

int main() {
  // Test that rounding is set to RNE
  if (FLT_ROUNDS == 1) {
    printf("Rounding: RNE \n");
  }
  // Set rounding to RTP
  fesetround(2);

  // Test if rounding is RTP or RNE
  if (FLT_ROUNDS == 2) { 
    printf("Rounding: RTP \n");
  } else if (FLT_ROUNDS == 1) {
    printf("Rounding: still RNE \n");
  }
}
