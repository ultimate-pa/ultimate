/*
 * Date: 2015-04-16
 * Author: Matthias Heizmann
 * 
 * In r14019 our tool incorrectly claims "comparison of incompatible pointers"
 * with the following failure path.
 * 
 * [L48]               char* str = (char*) malloc(1 * sizeof(char));
 *        VAL          [str={8:0}]
 * [L48]  EXPR, FCALL  malloc(1 * sizeof(char))
 *        VAL          [malloc(1 * sizeof(char))={6:0}, str={8:0}]
 * [L48]               char* str = (char*) malloc(1 * sizeof(char));
 *        VAL          [malloc(1 * sizeof(char))={6:0}, str={8:0}]
 * [L49]               char *s;
 *        VAL          [malloc(1 * sizeof(char))={6:0}, str={8:0}]
 * [L50]  EXPR         \read(*str)
 *        VAL          [\read(*str)={6:0}, malloc(1 * sizeof(char))={6:0}, str={8:0}]
 * [L50]               s = str
 * [L51]               s - str
 *        VAL          [\read(*str)=13, malloc(1 * sizeof(char))={6:0}, s={6:0}, str={8:0}]
 * 
 */
#include <stdlib.h>

int main() {
    char* str = (char*) malloc(1 * sizeof(char));
    char *s;
    s = str;
    return (s - str);
}


