extern void __VERIFIER_error() __attribute__ ((__noreturn__));

void printf(char *format);
void assert_fail(void);

int main() {
    int a;
    int *p1;

    p1 = &a;
    a = 5;

    a--;

    if (*p1 == 4) {
        printf("ERROR\n");
        assert_fail();
        goto ERROR;
    }

    return 0;

    ERROR: __VERIFIER_error();
    return 1;
}
