/*
 * Date: November 2013
 * Author: Christian Schilling
 * 
 * Void function call in if-then-else
 * expression does not work.
 */
void func() { }

int main() {
    (1 == 1) ? 0 : func();
    
    return 0;
}
