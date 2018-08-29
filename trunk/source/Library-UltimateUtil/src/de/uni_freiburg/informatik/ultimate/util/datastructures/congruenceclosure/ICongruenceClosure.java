package de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure;

import java.util.Collection;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public interface ICongruenceClosure<ELEM extends ICongruenceClosureElement<ELEM>> {

	IRemovalInfo<ELEM> getElementCurrentlyBeingRemoved();

	boolean isInconsistent();

	boolean isInconsistent(boolean close);

	boolean isTautological();

	boolean isFrozen();

	boolean isConstrained(ELEM elem);

	boolean isConstrainedDirectly(ELEM elem);

	void transformElementsAndFunctions(Function<ELEM, ELEM> transformer);

	Collection<ELEM> getAllElements();

//	void freezeAndClose();

//	void freezeIfNecessary();

	String toLogString();

	// methods used in assertions

	boolean assertSingleElementIsFullyRemoved(ELEM elem);

	boolean sanityCheckOnlyCc();

	boolean sanityCheckOnlyCc(IRemovalInfo<ELEM> remInfo);

	boolean reportEqualityRec(ELEM key, ELEM value);

	boolean reportDisequalityRec(ELEM key, ELEM value);

	void reportContainsConstraint(ELEM elem, Set<ELEM> literals);

//	SetConstraintConjunction<ELEM> getContainsConstraintForElement(ELEM elem);
	Set<SetConstraint<ELEM>> getContainsConstraintForElement(ELEM elem);

//	void reportContainsConstraint(ELEM elem, SetConstraintConjunction<ELEM> literalSet);
	void reportContainsConstraint(ELEM elem, Collection<SetConstraint<ELEM>> literalSet);

	Set<ELEM> getNodesToIntroduceBeforeRemoval(ELEM elemToRemove, Set<ELEM> elementsToRemove,
			Map<ELEM, ELEM> nodeToReplacementNode);

	boolean hasElement(ELEM n);

	boolean sanityCheck();

	boolean isDebugMode();

	ILogger getLogger();

	boolean addElement(ELEM proxyElem, boolean b);
}
