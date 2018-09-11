/*
2018-09-11 MH: Triggers unsupported operation exception in TypeHandler.cType2AstType(...) (see also https://github.com/ultimate-pa/ultimate/commit/338135fa39384f7d371b45ede4bbfc0a30d653c8)
-tc ../../../trunk/examples/toolchains/CheckedTranslation.xml 
-s ../../../trunk/examples/settings/default/automizer/svcomp-DerefFreeMemtrack-32bit-Automizer_Default.ep
*/
typedef struct myIncompleteStruct myNewName;
extern const myNewName myGlobalVar;

int main(void) {
	return 0;
}
