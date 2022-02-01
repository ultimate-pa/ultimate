#include <stdio.h>

int nondef(void);
void assume(int);

int gcd(int u, int v)
{
    int t;    
    assume (u >= 0);
    assume (v >= 0);
    while (u > 0) {
        if (u < v) {
            t = u;
            u = v;
            v = t;
        }
        u = u - v;
    }
    return v;
}

int main()
{
    int x = nondef(), y = nondef();
    if (x > 0 && y > 0) {
        printf("gcd(%d, %d) = %d\n", x, y, gcd(x, y));
    }
    return 0;
}
