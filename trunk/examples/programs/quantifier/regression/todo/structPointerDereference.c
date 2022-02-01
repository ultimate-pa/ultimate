/*
 * Date: November 2013
 * Author: Christian Schilling
 * 
 * A struct pointer in a struct is not correctly dereferenced.
 */
struct node {
    struct node *next;
    int value;
};

int main()
{
    struct node str;
    if(str.next->value == 0) {
        return 0;
    }
    return 0;
}
