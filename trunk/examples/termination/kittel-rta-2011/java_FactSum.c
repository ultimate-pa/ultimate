int factorial(int n) {
    if (n <=0) return 1;
    else return n*factorial(n-1);    
}

int doSum(int n) {
    int s=0;
    while (n >= 0) {
        s = s + factorial(n);
        n=n-1;
    }
    return s;
}

int main() {
    return doSum(10);
}
