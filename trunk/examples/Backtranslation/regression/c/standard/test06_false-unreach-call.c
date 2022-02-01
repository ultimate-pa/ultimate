extern void __VERIFIER_error() __attribute__ ((__noreturn__));

void printf(char *format);
void assert_fail(void);

void g(int **p1, int **p2) {
    int *pq = *p2;

    *p1 = *p2;
    *pq = 0;
}

int f(int a, int **p1, int **p2) {
    if (a == 4) {
        g(p1, p2);
        return 1;
    } else {
        return 0;
    }
}

int main() {
    int a, b;
    int *p1, *p2;

    p1 = &a;
    p2 = &b;

    b = 1;
    a = 5;

    a--;

    a = f(a, &p1, &p2);

    if (*p1 == 0) {
        printf("ERROR\n");
        assert_fail();
        goto ERROR;
    }

    return 0;

    ERROR: __VERIFIER_error();
    return 1;
}
