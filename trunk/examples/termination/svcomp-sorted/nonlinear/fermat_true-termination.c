int fermat (void) {
    const int MAX = 1000;
    int a = 1, b = 1, c = 1;
    while (1) {
        if (((a*a*a) == ((b*b*b)+(c*c*c)))) {
            return 1;
        }
        a++;
        if (a>MAX) {
            a = 1;
            b++;
        }
        if (b>MAX) {
            b = 1;
            c++;
        }
        if (c>MAX) {
            break;
        }
    }
    return 0;
}

int main() {
    return fermat();
}
