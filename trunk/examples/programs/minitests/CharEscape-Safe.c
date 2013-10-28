/*
 * Date: October 2013
 * Author: Christian Schilling and Matthias Heizmann
 * 
 */
int main() {
    char c1 = '\0';
    //@ assert c1 == 0;
    char c2 = '\\';
    char c3 = '\x5c';
    //@ assert c2 == c3;
    char c4 = '\7';
    char c5 = '\007';
    //@ assert c4 == c5;
    return 0;
}
