/*
 * Date: October 2013
 * Author: Christian Schilling
 * 
 * Auxiliary variable for struct offset is not declared.
 */
struct dummy {
    int a, b;
};

int main()
{
    struct dummy *pd1, *pd2;
    int i = pd1->a == pd2->b;

    return 0;
}
