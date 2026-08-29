/* #Safe
 *-----------------------------------------------------------------------------
 * Example with an anonymous struct and variables in a named (outer) struct
 *-----------------------------------------------------------------------------
 * Author: Manuel Bentele
 *   Date: 13.11.2025
 *---------------------------------------------------------------------------*/

struct foo {
    int a;
    struct {
        int b;
    };
    int c;
};

int main()
{
    struct foo f;
    f.a = 10;
    f.b = 20;
    f.c = 30;
    int a = f.a;
    int b = f.b;
    int c = f.c;
    //@ assert (a == 10 && b == 20 && c == 30);
    return f.a + f.b + f.c;
}
