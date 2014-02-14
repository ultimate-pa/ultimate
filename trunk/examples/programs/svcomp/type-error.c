/*
 * IllegalArgumentException: Unsupported primitive type (*type-error*)
 * 
 * Reason in CfgBuilder:
 * (NamedType[$Pointer$,[]]).boogieType == *type-error*
 * 
 * Both "int *l" and "char **argv" cause this error.
 */ 
int func(int *l) {
    return 0;
}

int main(int argc , char **argv) {
    return 0;
}
