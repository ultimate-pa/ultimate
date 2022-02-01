/*
 * Date: November 2013
 * Author: Christian Schilling
 * 
 * 'modifies' keyword is not transitive.
 */
char array[10];

int main() {
    int i;
    for (i = 0; i < sizeof(array); i++) {
        array[i] = 'a';
    }
    
    return 0;
}
