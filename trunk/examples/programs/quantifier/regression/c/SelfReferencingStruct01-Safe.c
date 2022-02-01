//#Safe
/*
 * Date: October 2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

#include <stdlib.h>

struct treeNode {
	int data;
	struct treeNode* leftChild;
	struct treeNode* rightChild;
};


int main() {
	struct treeNode* p = (struct treeNode*) malloc(sizeof(struct treeNode));
	p->data = 3;
	p->leftChild = p;
	p->rightChild = p;
	int a = p->data;
	//@ assert a == 3;
	free(p);
}
