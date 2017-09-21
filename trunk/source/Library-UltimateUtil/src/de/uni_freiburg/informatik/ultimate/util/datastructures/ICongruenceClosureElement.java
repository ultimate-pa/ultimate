package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.Set;

public interface ICongruenceClosureElement<ELEM extends ICongruenceClosureElement<ELEM>> {

	boolean hasSameTypeAs(ELEM other);

	boolean isFunctionApplication();

	ELEM getAppliedFunction();

	ELEM getArgument();

	void addAfParent(ELEM parent);

	void addArgParent(ELEM parent);

	Set<ELEM> getAfParents();

	Set<ELEM> getArgParents();

	int getHeight();
}
