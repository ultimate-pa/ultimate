/*
 * Test concerning the scoping of typedefs
 * the Variable ul should be of type unsigned long,
 * while u is of array type
 * author: nutz, 18.12.2013
 */
typedef unsigned long ulong;
ulong ulongVar;

int main() {
	ulong ul = 1;

	typedef unsigned long ulong[5];

	ulong u = {'a'};
}
