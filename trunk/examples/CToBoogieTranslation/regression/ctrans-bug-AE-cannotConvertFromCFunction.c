/*
Example for 
java.lang.AssertionError: cannot convert to CFunction
        at de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer.convert(ExpressionResultTransformer.java:593)
2018-10-01 DD 
*/
void foo()
{
  int (**x)();
  *x = 0;
}

