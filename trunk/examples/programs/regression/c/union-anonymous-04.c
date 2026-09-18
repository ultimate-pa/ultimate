/* #Safe
 *-----------------------------------------------------------------------------
 * Example with an anonymous union in an outer union as part of a typedef
 *-----------------------------------------------------------------------------
 * Author: Manuel Bentele
 *   Date: 13.11.2025
 *---------------------------------------------------------------------------*/

typedef union {
    int a;
    union {
        int b;
        int c;
    };
} foo_t;

int main()
{
    foo_t f;
    f.a = 10;
    f.b = 20;
    f.c = 30;
    int a = f.a;
    int b = f.b;
    int c = f.c;
    //@ assert (a == 30 && b == 30 && c == 30);
    return f.a + f.b + f.c;
}
