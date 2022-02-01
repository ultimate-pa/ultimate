/*
 * Date: November 2013
 * Author: Christian Schilling
 * 
 * Array becomes global and is modified,
 * but 'modifies' keyword is not added.
 */
int main() {
    static char array[10];
    int i;
    for (i = 0; i < sizeof(array); i++) {
        array[i] = 'a';
    }
    
    return 0;
}
