/*
 * Date: November 2013
 * Author: Christian Schilling
 * 
 * Recursive struct.
 * Problem: node is considered an incomplete struct
 * and hence the offset constants are not declared.
 */

#include <stdlib.h>

typedef struct node {
  int h;
  struct node *n;
} *List;

int main() {
  List t;
  t = (List) malloc(sizeof(struct node));
  t->h = 1;
}
