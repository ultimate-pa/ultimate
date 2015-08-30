/*
 * Date: October 2013
 * Author: Christian Schilling
 * NullPointerException in CHandler:
 * assert (tmpIType.equals(reNegative.expr.getType()));
 * -> reNegative.expr == null
 * 
 * gcc -std=c99 -pedantic
 *   says
 * warning: ISO C forbids conditional expr with only one void side [-pedantic]
 */

void func() {
    return;
}

int main() {
    ((1 == 1) ? 0 : func());
    return 0;
}
