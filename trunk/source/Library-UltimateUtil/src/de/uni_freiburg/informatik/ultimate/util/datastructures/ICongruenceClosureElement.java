package de.uni_freiburg.informatik.ultimate.util.datastructures;

public interface ICongruenceClosureElement<ELEM extends ICongruenceClosureElement<ELEM>> {

	boolean hasSameTypeAs(ELEM other);

	boolean isFunctionApplication();

	ELEM getAppliedFunction();

	ELEM getArgument();

//	void addAfParent(ELEM parent);
//
//	void addArgParent(ELEM parent);
//
//	void removeAfParent(ELEM parent);
//
//	void removeArgParent(ELEM parent);
//
//	Set<ELEM> getAfParents();
//
//	Set<ELEM> getArgParents();

	ELEM replaceAppliedFunction(ELEM replacer);

	ELEM replaceArgument(ELEM replacer);

//	int getHeight();

	boolean isLiteral();
}
