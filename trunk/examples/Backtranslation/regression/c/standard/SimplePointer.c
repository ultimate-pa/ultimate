extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int main() {
    int a;
    int *p1;

    p1 = &a;
    a = 5;

    a--;

    if (*p1 == 4) {
        goto ERROR;
    }

    return 0;

    ERROR: __VERIFIER_error();
    return 1;
}
