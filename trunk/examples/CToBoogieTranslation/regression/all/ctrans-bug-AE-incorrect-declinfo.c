/*
2018-09-18 DD: Minimal example that triggers the following exception. 

-tc any toolchain with C translation and Boogie Preprocessor 
-s settings/default/automizer/svcomp-Reach-32bit-Automizer_Bitvector.epf

[2018-09-18 16:58:14,516 FATAL L292        ToolchainWalker]: The Plugin de.uni_freiburg.informatik.ultimate.boogie.preprocessor has thrown an exception:
java.lang.AssertionError: Incorrect DeclarationInformation of #valueAsBitvector. Expected: QUANTIFIED   Found: <PROC_FUNC_OUTPARAM,write~intFLOATTYPE8>
        at de.uni_freiburg.informatik.ultimate.boogie.typechecker.TypeCheckHelper.internalError(TypeCheckHelper.java:293)

*/
typedef union {
  double value;

} ieee_double_shape_type;

void copysign_double(    ) {

    ieee_double_shape_type gh_u;
    gh_u.value = 0;

}
