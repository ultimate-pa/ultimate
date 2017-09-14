package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.List;

public interface ICongruenceClosureElement<ELEM extends ICongruenceClosureElement<ELEM>> {

	boolean isFunction();

	boolean hasSameTypeAs(ELEM other);

	boolean isFunctionApplication();

	ELEM getAppliedFunction();

	List<ELEM> getArguments();

}
