package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.List;

public interface ICongruenceClosureElement<ELEM extends ICongruenceClosureElement<ELEM, FUNCTION>, FUNCTION> {

	boolean isFunctionApplication();

	FUNCTION getAppliedFunction();

	List<ELEM> getArguments();

}
