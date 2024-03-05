//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2023-03-09
//
// Test support for stdnoreturn.h
//
// Unclear whether we want to fully support this, we just don't want to crash.
//
// The function specifier `_Noreturn` and the macro `noreturn` are deprecated 
// in C23 and should be replaced by the noreturn attribute.

_Noreturn void func01() {
    while (1) {}
}

int main() {
    func01();
    return 0;
}

