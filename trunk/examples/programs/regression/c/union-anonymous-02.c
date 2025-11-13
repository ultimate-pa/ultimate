/* #Safe
 *-----------------------------------------------------------------------------
 * Example with an anonymous union and variables in a named (outer) struct
 *-----------------------------------------------------------------------------
 * Author: Manuel Bentele
 *   Date: 13.11.2025
 *---------------------------------------------------------------------------*/

struct foo {
    int a;
    union {
        int b;
        int c;
    };
    int d;
};

int main()
{
    struct foo f;
    f.a = 10;
    f.b = 20;
    f.c = 30;
    f.d = 40;
    int a = f.a;
    int b = f.b;
    int c = f.c;
    int d = f.d;
    //@ assert (a == 10 && b == 30 && c == 30 && d == 40);
    return f.a + f.b + f.c + f.d;
}
