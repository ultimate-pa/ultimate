//#Safe
/*
 * Test exposing a former bug with malloc calls as function call arguments. An auxiliary variable was created but not
 * handled properly, leading to an assertion violation in FunctionHandler.
 */

extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

int test(void* ptr) {
  return *((int*)ptr);
}

int main() {
  int x = test( malloc(42) );
  return x;
}
