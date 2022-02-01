//#Safe
/*
 * Bug in r9906 sizeof roflcopter leads to Exception
 * Bug in later versions sizeof(node*) translated to the same constant
 * as sizeof(node).
 * 
 * Date: October 2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

typedef struct {
	int num;
	int denom;
} fraction;

typedef fraction bruch;



typedef struct node {
  int h;
  struct node *n;
} *List;

int main() {
    int fractionSize = sizeof(fraction);
	int intSize = sizeof(int);
    //@ assert fractionSize >= intSize;
	
	int bruchSize = sizeof(bruch);
	//@ assert bruchSize == fractionSize;
	
	int nodeSize = sizeof(struct node);
	//@ assert nodeSize > 0;
	
	int ptrSize = sizeof(int*);
	//@ assert ptrSize > 0;
	//@ assert nodeSize >= intSize + ptrSize;
	//@ assert nodeSize > ptrSize;
	
	int listSize = sizeof(List);
	//@ assert ptrSize == ptrSize;
	
	int nodePtrSize = sizeof(struct node*);
	//@ assert nodePtrSize == ptrSize;

}


// don't know if the roflcopter is needed any more
typedef struct roflcopter {
	int rotorBlades;
	
} lol;