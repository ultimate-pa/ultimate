//#iSafe
/*
 * Bug in r9906 sizeof roflcopter leads to Exception
 * Bug in later versions sizeof(node*) translated to the same constant
 * as sizeof(node).
 * 
 * Date: October 2013
 * Author: heizmann@informtik.uni-freiburg.de
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
    int* a; // some auxiliary statement to obtain memory model
    int b = *a; // some auxiliary statement to obtain memory model
    
    int fractionSize = sizeof(fraction);
	int intSize = sizeof(int);
    //@ assert fractionSize >= 2 * intSize;
	
	int bruchSize = sizeof(bruch);
	//@ assert bruchSize == fractionSize;
	
	int nodeSize = sizeof(node);
	//@ assert nodeSize > 0;
	int ptrSize = sizeof(node*);
	//@ assert ptrSize > 0;
	
	//@ assert nodeSize >= intSize + ptrSize;
	// assert nodeSize > ptrSize;
}


// don't know if the roflcopter is needed any more
typedef struct roflcopter {
	int rotorBlades;
	
} lol;