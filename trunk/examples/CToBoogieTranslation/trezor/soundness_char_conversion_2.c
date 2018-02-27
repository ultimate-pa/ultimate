char foo() {
    return '\xff';
}
int main(void) {
    char c = (char) foo();
    int ic = (int)c;
    // this should not happen
    //@assert ic < 128 && ic > 128;
    return 0;
}
