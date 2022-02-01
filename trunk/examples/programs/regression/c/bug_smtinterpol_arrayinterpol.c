//#Safe 
/*
2017-12-06 DD

Example for array interpolation bug in SMTInterpol

java.lang.NullPointerException
        at de.uni_freiburg.informatik.ultimate.logic.Theory.term(Theory.java:1441)
        at de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.ArrayInterpolator$WeakPathInfo$WeakPathEnd.buildRecursiveInterpolantBPath(ArrayInterpolator.java:2116)
        at de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.ArrayInterpolator$WeakPathInfo$WeakPathEnd.buildRecursiveInterpolant(ArrayInterpolator.java:1888)
        at de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.ArrayInterpolator$WeakPathInfo.interpolateStorePathInfoExt(ArrayInterpolator.java:930)
        at de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.ArrayInterpolator.computeWeakeqExtInterpolants(ArrayInterpolator.java:271)
        at de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.ArrayInterpolator.computeInterpolants(ArrayInterpolator.java:169)
        at de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.walkLeafNode(Interpolator.java:287)

*/
void main() {
  void* p =  __builtin_alloca (0);
}

