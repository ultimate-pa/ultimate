/* #Safe
 *-----------------------------------------------------------------------------
 * Example with nested anonymous unions in a named (outer) struct
 *-----------------------------------------------------------------------------
 * Author: Manuel Bentele
 *   Date: 13.11.2025
 *---------------------------------------------------------------------------*/

struct foo {
    union {
        int a;
        union {
            int b;
            int c;
        };
    };
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
    //@ assert (a == 30 && b == 30 && c == 30);
    return f.a + f.b + f.c;
}
