void g(int);
void h(int);
void j(int);

void f(int x) {
    if (x > 0) {
        g(x - 1);
    }
}

void g(int x) {
    h(x - 1);
}

void h(int x) {
    j(x - 1);
}

void j(int x) {
    f(x - 1);
}
