/**
 * Global constant initializer requires aux var, which is then incorrectly classified as GLOBAL, leading to illegal
 *  modifies ..., #t~nondet0, ...
 *
 */

static const float huge_ceil = 1.0e30;

int main() {
  return 0;
}