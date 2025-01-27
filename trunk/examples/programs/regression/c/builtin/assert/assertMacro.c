//#Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2023-03-08
// Test support for assert.h

#include <assert.h>

int g = 23;

int main() {
    assert(g == 42);
    return 0;
}
