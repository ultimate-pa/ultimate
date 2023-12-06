//#Safe
/*
 * Valid C23 static assertion
 * 
 * Author: Manuel Bentele
 *   Date: 2023-08-11
 */

int main() {
    int i = 0;
    static_assert(1 == 1);
    return i;
}
