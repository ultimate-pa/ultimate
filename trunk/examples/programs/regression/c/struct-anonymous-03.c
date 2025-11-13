/* #Safe
 *-----------------------------------------------------------------------------
 * Example with nested anonymous structs in a named (outer) struct
 *-----------------------------------------------------------------------------
 * Author: Manuel Bentele
 *   Date: 13.11.2025
 *---------------------------------------------------------------------------*/

struct foo {
    struct {
        int a;
        struct {
            int b;
        };
    };
};

int main()
{
    struct foo f;
    f.a = 10;
    f.b = 20;
    int a = f.a;
    int b = f.b;
    //@ assert (a == 10 && b == 20);
    return f.a + f.b;
}
