/* #Safe
 *-----------------------------------------------------------------------------
 * Example with an anonymous struct in an outer union as part of a typedef
 *-----------------------------------------------------------------------------
 * Author: Manuel Bentele
 *   Date: 13.11.2025
 *---------------------------------------------------------------------------*/

typedef union {
    struct {
        unsigned int a : 8;
        unsigned int b : 8;
        unsigned int c : 8;
        unsigned int d : 8;
    };
    unsigned int all;
} foo_t;

int main()
{
    foo_t f;
    f.a = 10;
    f.b = 20;
    f.c = 30;
    f.d = 40;
    int a = f.a;
    int b = f.b;
    int c = f.c;
    int d = f.d;
    int all = f.all;
    assert (a == 10 && b == 20 && c == 30 && d == 40 && all == 673059850);
    return f.all;
}
