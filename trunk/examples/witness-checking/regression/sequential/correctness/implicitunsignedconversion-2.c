extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "implicitunsignedconversion-2.c", 3, "reach_error"); }

int main() {
  unsigned int plus_one = 1;
  int minus_one = -1;

  if(plus_one > minus_one) {
    goto ERROR;
  }
  
  return (0);
  ERROR: {reach_error();abort();}
  return (-1);
}

