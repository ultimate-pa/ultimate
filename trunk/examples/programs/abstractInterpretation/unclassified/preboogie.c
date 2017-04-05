int fibo(int n) {
        if (n == 0) ; else {
        return fibo(n-1) + fibo(n-1);
    }
}

void main( ) {
    int x = 10;
    fibo(x);

	ERROR: __VERIFIER_error();

}