// #Unsafe
/*
 * longjmp out of nested calls back into main, the resumed setjmp returns 3, not 0.
 *
 * Date: 2026-11-17
 * Author: Max.Barth@lmu.de
 *
 */
extern int setjmp(jmp_buf env);
extern void longjmp(jmp_buf env, int val);

jmp_buf env;
int count = 0;

void g() {
  longjmp(env, 3);
}

void f() {
  g();
}

int main() {
  int val = setjmp(env);
  count++;
  if (count == 2 && val != 0) {
    reach_error();
  }
  if (count < 2) {
    f();
  }
  return 0;
}
