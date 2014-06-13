void g(int);

void f(int x) {
    if (x > 0) {
        g(x - 1);
    }
}

void g(int x) {
    f(x - 1);
}
