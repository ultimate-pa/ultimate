package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.List;
import java.util.Set;

public interface ICongruenceClosureElement<
		ELEM extends ICongruenceClosureElement<ELEM, FUNCTION>,
//		BASEELEM extends ICongruenceClosureElement<BASEELEM, FUNCAPPELEM, FUNCTION>,
//		FUNCAPPELEM extends ICongruenceClosureFunctionApplication<BASEELEM, FUNCAPPELEM, FUNCTION>,
//		FUNCTION extends ICongruenceClosureFunction
		FUNCTION
		>
			 {

	void addParent(ELEM parent);

	Set<ELEM> getParents();

	boolean isFunctionApplication();

	FUNCTION getAppliedFunction();

	List<ELEM> getArguments();

}
