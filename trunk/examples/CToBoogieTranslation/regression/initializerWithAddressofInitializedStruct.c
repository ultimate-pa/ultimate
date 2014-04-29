//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 25.04.2013
// Bug: We are unable to translate the initialization of the struct (where
// the address is used as value of a field).

struct list {
	int element;
	struct list *next;
};

int main()
{
	struct list selfloop = { 0, &(selfloop) };
	int equal = (selfloop.next == &selfloop);
	//@ assert equal != 0;
	return 0;
}
