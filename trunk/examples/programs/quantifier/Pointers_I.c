#include <stdlib.h>

struct _int
{
	int x;
	int y;
};

typedef struct _int integer;

/*@ ensures \valid(\result);
 ensures \result->x==10 && \result->y==20;
 */
integer* init();

/*@ requires \valid(n);
 ensures \valid(n) && \valid(*n);
 ensures (*n)->x == 30 && (*n)->y == 50;
 */
void init2(integer **n);

/*@ requires \valid(n);
 ensures \valid(n);
 ensures \old(n->x) == n->x && \old(n->y) == n->y;
 */
void print(integer *n);

/*@ requires \valid(n);
 ensures !\valid(n);
 */
void free_mem(integer *n);

integer* init()
{
	integer* n = (integer *) malloc(sizeof(integer));
//	n->x = 10;
//	n->y = 20;
	return n;
}

//void init2(integer **n)
//{
//	*n = (integer *) malloc(sizeof(integer));
////	(*n)->x = 30;
////	(*n)->y = 40;
////	(**n).x = 50;
//}

void print(integer *n)
{
	//printf("X: %d; Y: %d\n", n->x, n->y);
}

void free_mem(integer *n)
{
	free(n);
}

int main()
{
	integer* my_int = init();
	integer* my_int2;
//	init2(&my_int2);
	print(my_int);
	print(my_int2);
	free_mem(my_int);
	free_mem(my_int2);
}
