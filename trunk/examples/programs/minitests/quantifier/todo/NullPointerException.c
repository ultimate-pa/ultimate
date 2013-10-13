/*
 * NullPointerException in CHandler:
 * assert (tmpIType.equals(reNegative.expr.getType()));
 * -> reNegative.expr == null
 */

void func() {
    return;
}

void main() {
    ((1 == 1) ? 0 : func());
}
