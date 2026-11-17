// #Safe
/*
 * longjmp(env, 0) makes setjmp return 1. Two buffers are distinguished, the
 * second setjmp in the same function overwrites nothing of the first one.
 *
 * Date: 2026-11-17
 * Author: Max.Barth@lmu.de
 *
 */
extern int setjmp(jmp_buf env);
extern void longjmp(jmp_buf env, int val);

jmp_buf a;
jmp_buf b;
int phase = 0;

void jump(int which) {
  if (which == 0) {
    longjmp(a, 0);
  } else {
    longjmp(b, 7);
  }
}

int main() {
  int x = setjmp(a);
  if (phase == 1) {
    if (x != 1) {
      reach_error();
    }
  }
  int y = setjmp(b);
  if (phase == 2) {
    if (y != 7 || x != 1) {
      reach_error();
    }
    return 0;
  }
  phase++;
  jump(phase == 1 ? 0 : 1);
  reach_error();
  return 0;
}
