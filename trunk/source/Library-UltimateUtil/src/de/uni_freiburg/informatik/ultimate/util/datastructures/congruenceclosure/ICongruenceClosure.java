package de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure;

import java.util.Collection;
import java.util.function.Function;

public interface ICongruenceClosure<ELEM extends ICongruenceClosureElement<ELEM>> {

	IRemovalInfo<ELEM> getElementCurrentlyBeingRemoved();

	boolean isInconsistent();

	boolean isTautological();

	boolean isFrozen();

	boolean isConstrained(ELEM elem);

	void transformElementsAndFunctions(Function<ELEM, ELEM> transformer);

	Collection<ELEM> getAllElements();

	void freeze();

	String toLogString();

	// methods used in assertions

	boolean assertSingleElementIsFullyRemoved(ELEM elem);

	boolean sanityCheckOnlyCc();

	boolean sanityCheckOnlyCc(IRemovalInfo<ELEM> remInfo);

}
