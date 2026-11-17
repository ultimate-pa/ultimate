// #Safe
/*
 * longjmp out of nested calls back into main. Locals of main keep their values,
 * setjmp returns the value passed to longjmp.
 *
 * Date: 2026-11-17
 * Author: Max.Barth@lmu.de
 *
 */
extern int setjmp(jmp_buf env);
extern void longjmp(jmp_buf env, int val);

jmp_buf env;
int global = 0;

void g(int x) {
  global = x;
  longjmp(env, 3);
  reach_error();
}

int f(int x) {
  g(x + 1);
  reach_error();
  return 0;
}

int main() {
  int local = 0;
  int val = setjmp(env);
  if (val == 0) {
    local = 5;
    f(1);
    reach_error();
  }
  if (val != 3 || local != 5 || global != 2) {
    reach_error();
  }
  return 0;
}
