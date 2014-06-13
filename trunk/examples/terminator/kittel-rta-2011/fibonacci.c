long fibonacci(long n)
{
    if (n < 2L) {
        return n;
    } else { 
        return fibonacci(n - 1L) + fibonacci(n - 2L);
    }
}
