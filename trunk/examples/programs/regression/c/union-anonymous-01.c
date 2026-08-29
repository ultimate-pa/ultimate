/* #Safe
 *-----------------------------------------------------------------------------
 * Example with an anonymous union in a named (outer) struct
 *-----------------------------------------------------------------------------
 * Author: Manuel Bentele
 *   Date: 13.11.2025
 *---------------------------------------------------------------------------*/

struct foo {
    union {
        int a;
        int b;
    };
};

int main()
{
    struct foo f;
    f.a = 10;
    f.b = 20;
    int a = f.a;
    int b = f.b;
    //@ assert (a == 20 && b == 20);
    return f.a + f.b;
}
