//#Safe
/*
 * Author: Max Fleischer 
 * Date: 2025-09-15
 *
 * See https://github.com/ultimate-pa/ultimate/issues/747
 */

extern int i;
int i;
int main(){
    if(i != 0) __VERIFIER_error();
}
