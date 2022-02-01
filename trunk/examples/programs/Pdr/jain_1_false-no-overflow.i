extern void __VERIFIER_error() __attribute__ ((__noreturn__));

extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int main()
{
  int y;

  y = 1;

  while(1)
    {
      y = y +2*__VERIFIER_nondet_int();


      __VERIFIER_assert (y!=0);

    }
    return 0;
}
