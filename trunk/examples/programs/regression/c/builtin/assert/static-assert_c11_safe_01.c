//#Safe
/*
 * Valid C11 static assertion (deprecated in C23)
 * 
 * Author: Manuel Bentele
 *   Date: 2023-08-11
 */

int main() {
    int i = 0;
    _Static_assert(1 == 1);
    return i;
}
