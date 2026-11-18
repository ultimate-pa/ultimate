// #Safe
/*
 * Every activation of the recursive function executes the same setjmp. The longjmp
 * targets the buffer of the outermost activation, so it has to unwind through the
 * inner activations (which have the same setjmp site) and resume in the outermost one.
 *
 * Date: 2026-11-17
 * Author: Max.Barth@lmu.de
 *
 */
typedef struct { long regs[8]; int mask; } jmp_buf[1];
extern int _setjmp(jmp_buf env);
extern void longjmp(jmp_buf env, int val);

jmp_buf *outermost;

int rec(int depth) {
  jmp_buf here;
  if (_setjmp(here) != 0) {
    if (depth != 0) {
      reach_error();
    }
    return 42;
  }
  if (depth == 0) {
    outermost = &here;
  }
  if (depth < 2) {
    rec(depth + 1);
    // rec never returns normally
    reach_error();
  }
  longjmp(*outermost, 1);
  return -1;
}

int main() {
  if (rec(0) != 42) {
    reach_error();
  }
  return 0;
}
