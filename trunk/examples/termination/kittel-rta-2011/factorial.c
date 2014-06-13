long factorial(long n)
{
    if(n < 2L) {
        return n;
    } else {
        return n*factorial(n - 1L);
    }
}
