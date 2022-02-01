package de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure;

import java.util.Map;
import java.util.Set;

/**
 * Abstracts from {@link EqNode} and {@link StringCcElement} (the latter is used for testing purposes)
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ELEM>
 */
public interface ICongruenceClosureElement<ELEM extends ICongruenceClosureElement<ELEM>> {

	boolean hasSameTypeAs(ELEM other);

	boolean isFunctionApplication();

	ELEM getAppliedFunction();

	ELEM getArgument();

	ELEM replaceAppliedFunction(ELEM replacer);

	ELEM replaceArgument(ELEM replacer);

	ELEM replaceSubNode(Map<ELEM, ELEM> replacementMapping);

	boolean isLiteral();

	/**
	 * (isFunctionApplication must  return false if this is true)
	 *
	 * @return true iff this element depends on some other element (i.e., changes to another element may affect this
	 *  element), <b>and</b> this dependency is not modeled as a function application by us 	 */
	boolean isDependentNonFunctionApplication();

	/**
	 * Should only be called if this id is a dependent id. Returns all supporters of this id.
	 * A supporter is an id that a dependent id depends on.
	 * @return
	 */
	Set<ELEM> getSupportingNodes();

	/**
	 * (isFunctionApplication must  return false if this is true)
	 *
	 * @return true if this is a constant function
	 */
	default boolean isConstantFunction() {
		// default case, override this in the classes that are a constant function
		return false;
	}

	default ELEM getConstantFunctionValue() {
		// default case, override this in the classes that are a constant function
		throw new UnsupportedOperationException("not a constant function");
	}

	/**
	 * (isFunctionApplication must  return false if this is true)
	 *
	 * @return true if this is a mix function (i.e. a function that nondeterministically has the value of one or
	 *  another function).
	 */
	default boolean isMixFunction() {
		// default case, override this in the classes that are a constant function
		return false;
	}

	default ELEM getMixFunction1() {
		// default case, override this in the classes that are a constant function
		throw new UnsupportedOperationException("not a constant function");
	}

	default ELEM getMixFunction2() {
		// default case, override this in the classes that are a constant function
		throw new UnsupportedOperationException("not a constant function");
	}

}
