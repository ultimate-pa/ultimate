//#Safe
/*
 * Currently (Nov 2017) we cannot pass sideeffects from declarators.
 * In this case the declarator should insert an assertion into the Boogie code 
 * that checks for division-by-0.
 *
 * snippet from
 * trunk/examples/svcomp/ntdrivers/floppy_true-unreach-call_true-valid-memsafety.i.cil.c \
 *
 */

typedef unsigned short wchar_t;

typedef wchar_t WCHAR;

struct _VPB {
   WCHAR VolumeLabel[(32U * sizeof(WCHAR )) / sizeof(WCHAR )] ;
};

int main() {
  struct _VPB vpb;
}
