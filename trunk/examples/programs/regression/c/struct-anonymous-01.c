/* #Safe
 *-----------------------------------------------------------------------------
 * Example with an anonymous struct in a named (outer) struct
 *-----------------------------------------------------------------------------
 * Author: Manuel Bentele
 *   Date: 13.11.2025
 *---------------------------------------------------------------------------*/

struct foo {
    struct {
        int a;
    };
};

int main()
{
    struct foo f;
    f.a = 10;
    int a = f.a;
    //@ assert (a == 10);
    return f.a;
}
