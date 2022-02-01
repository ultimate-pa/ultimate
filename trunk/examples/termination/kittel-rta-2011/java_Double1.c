void test(int n) {
    int i;
    for (i = 0; i < n; i++)
        test(i);
}

int main() {
    test(10);
    return 0;
}
