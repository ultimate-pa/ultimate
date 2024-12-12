//#Safe
/*
 * Valid assertion expression composed of subterms and a string literal.
 * 
 * Author: Manuel Bentele
 *   Date: 2023-11-10
 */

int main()
{
    int a = 0;
    int b = 1;

    assert(a != b && "Error message!");

    return 0;
}
