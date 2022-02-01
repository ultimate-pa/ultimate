/**
 * Tests if the translation can handle a sizeof operation on an expression that
 * is a dereference of a void pointer (thus the expression has type void).
 *
 * This is not strictly in the C standard, since void is an incomplete type,
 * but GCC and consorts tend to translate it the same as sizeof(char).
 *
 * @author nutz@cs.uni-freiburg.de
 */
int main() {
  void *p;
  size_t s = sizeof(*p);
  return 0;
}
