void test(int n) {
    int i;
    for (i = n - 1; i >= 0; i--)
        test(i);
}

int main() {
    test(10);
    return 0;
}
