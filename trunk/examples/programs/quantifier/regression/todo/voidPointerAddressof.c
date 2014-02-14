/*
 * Date: November 2013
 * Author: Christian Schilling
 * 
 * addressof (&) on void pointer is not supported.
 */
int main() {
    void *p;
    &p;
    
    return 0;
}
