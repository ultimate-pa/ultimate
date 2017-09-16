package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.Set;

public interface ICongruenceClosureElement<ELEM extends ICongruenceClosureElement<ELEM>> {

//	boolean isFunction();

	boolean hasSameTypeAs(ELEM other);

	boolean isFunctionApplication();

	ELEM getAppliedFunction();

	ELEM getArgument();

	void addParent(ELEM parent);

	Set<ELEM> getParents();

//	/**
//	 * list of leaves of this tree, in order
//	 *
//	 * this includes the leftmost leaf, i.e., the atomic function symbol
//	 *
//	 * @return
//	 */
//	ELEM[] getArguments();

	int getHeight();
}
