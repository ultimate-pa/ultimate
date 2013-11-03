/*
 * Date: November 2013
 * Author: Christian Schilling
 * 
 * Array passed as function parameter
 * leads leads to a ClassCastException.
 */
void func(int arr[]) {
    arr[0] = 1;
}

int main () {
    return 0;
}
