/*
 * 2016-12-12 DD
 * de.uni_freiburg.informatik.ultimate.boogie.preprocessor: IllegalArgumentException: ASTType is null - cannot resolve type.: de.uni_freiburg.informatik.ultimate.boogie.preprocessor.TypeManager.resolveType(TypeManager.java:176)
 * Extracted from svcomp/loops/bubble_sort_false-unreach-call.i
 *
 * Ok according to gcc -std=c11 --pedantic (4.9.3)
 */
int main()
{
	0 ? (void)0 : (void)0;
}