void test(int n) {
    while (--n > 0) test(n);
}

int main() {
    test(10);
    return 0;
}
