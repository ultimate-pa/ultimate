/*
* This test is shows that the rounding mode in c is not changed
* add the -lm option when compiling this with gcc or fesetround 
* and fegetround can throw a undefined reference error
*/

#include <math.h>
#include <stdio.h>
#include <fenv.h>
#include <float.h>

int main() {

  int set_round_ok = 0;
  int test_number = 1;
  char test[] = ". Test:";
  
  // Test the default setup
  printf("Default Settings:\n");
  int save_round = fegetround();
  if (save_round == 0) {
    printf("%d", test_number); 
    printf("%s succeded\n", test);
  }
  test_number += 1;

  if (set_round_ok == 0) {
    printf("%d", test_number); 
    printf("%s setround succesfull\n", test);
  }
  test_number += 1;
  
  if (FLT_ROUNDS == 1) {
    printf("%d", test_number); 
    printf("%s succeded\n", test);
  }
  test_number += 1;

  // Tests for FE_UPWARD starts with 4.
  printf("Set Rounding Mode to towards positive:\n");  
  fesetround(FE_UPWARD);
  set_round_ok = fesetround(FE_UPWARD);
  save_round = fegetround();
  if (save_round == 2) {
    printf("%d", test_number); 
    printf("%s succeded\n", test);
  }
  test_number += 1;

  if (set_round_ok == 1) {
    printf("%d", test_number); 
    printf("%s setround succesfull\n", test);
    set_round_ok = 0;
  }
  test_number += 1;
  
  if (FLT_ROUNDS == 2) {
    printf("%d", test_number); 
    printf("%s succeded\n", test);
  }
  test_number += 1;

  // Test for 2 should be UPWARDS starts with 7.
  fesetround(2);
  set_round_ok = fesetround(2);
  save_round = fegetround();
  if (save_round == 2) {
    printf("%d", test_number); 
    printf("%s succeded\n", test);
  }
  test_number += 1;

  if (set_round_ok == 1) {
    printf("%d", test_number); 
    printf("%s setround succesfull\n", test);
    set_round_ok = 0;
  }
  test_number += 1;
  
  if (FLT_ROUNDS == 2) {
    printf("%d", test_number); 
    printf("%s succeded\n", test);
  }
  test_number += 1;

  // Tests for FE_TOWARDZERO starts with 10.i
  printf("Set Rounding Mode to towards Zero:\n");
  fesetround(FE_TOWARDZERO);
  set_round_ok = fesetround(FE_TOWARDZERO);
  save_round = fegetround();
  if (save_round == 0) {
    printf("%d", test_number); 
    printf("%s succeded\n", test);
  }
  test_number += 1;

  if (set_round_ok == 1) {
    printf("%d", test_number); 
    printf("%s setround succesfull\n", test);
    set_round_ok = 0;
  }
  test_number += 1;
  
  if (FLT_ROUNDS == 0) {
    printf("%d", test_number); 
    printf("%s succeded\n", test);
  }
  test_number += 1;

  // Test for 0 should be ZERO starts with 13.
  fesetround(0);
  set_round_ok = fesetround(0);
  save_round = fegetround();
  if (save_round == 0) {
    printf("%d", test_number); 
    printf("%s succeded (this is a false positive since this tested value hasn't changed since the start)\n", test);
  }
  test_number += 1;

  if (set_round_ok == 1) {
    printf("%d", test_number); 
    printf("%s setround succesfull\n", test);
    set_round_ok = 0;
  }
  test_number += 1;
  
  if (FLT_ROUNDS == 0) {
    printf("%d", test_number); 
    printf("%s succeded\n", test);
  }
  test_number += 1;

  // Tests for FE_DOWNWARD starts with 16.
  printf("Set Rounding to downwards:\n");
  fesetround(FE_DOWNWARD);
  set_round_ok = fesetround(FE_DOWNWARD);
  save_round = fegetround();
  if (save_round == 3) {
    printf("%d", test_number); 
    printf("%s succeded\n", test);
  }
  test_number += 1;

  if (set_round_ok == 1) {
    printf("%d", test_number); 
    printf("%s setround succesfull\n", test);
    set_round_ok = 0;
  }
  test_number += 1;
  
  if (FLT_ROUNDS == 3) {
    printf("%d", test_number); 
    printf("%s succeded\n", test);
  }
  test_number += 1;

  // Test for 3 should be DOWNWARD starts with 19.
  fesetround(3);
  set_round_ok = fesetround(3);
  save_round = fegetround();
  if (save_round == 3) {
    printf("%d", test_number); 
    printf("%s succeded\n", test);
  }
  test_number += 1;

  if (set_round_ok == 1) {
    printf("%d", test_number); 
    printf("%s setround succesfull\n", test);
    set_round_ok = 0;
  }
  test_number += 1;
  
  if (FLT_ROUNDS == 3) {
    printf("%d", test_number); 
    printf("%s succeded\n", test);
  }
  test_number += 1;
}
