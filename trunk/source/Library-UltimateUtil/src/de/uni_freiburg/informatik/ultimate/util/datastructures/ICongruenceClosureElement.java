package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.Set;

public interface ICongruenceClosureElement<ELEM extends ICongruenceClosureElement<ELEM>> {

	boolean hasSameTypeAs(ELEM other);

	boolean isFunctionApplication();

	ELEM getAppliedFunction();

	ELEM getArgument();

	void addParent(ELEM parent);

	Set<ELEM> getParents();

	int getHeight();
}
