package de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;

public interface ICcRemoveElement<ELEM extends ICongruenceClosureElement<ELEM>> {

	boolean isInconsistent();

	boolean hasElement(ELEM elem);

	Set<ELEM> collectElementsToRemove(ELEM elem);

	ELEM getOtherEquivalenceClassMember(ELEM elemToRemove, Set<ELEM> elementsToRemove);

	boolean isConstrained(ELEM elemToRemove);

	Set<ELEM> getNodesToIntroduceBeforeRemoval(ELEM elemToRemove, Set<ELEM> elementsToRemove,
			Map<ELEM, ELEM> nodeToReplacementNode);

	boolean addElementRec(ELEM proxyElem);

	boolean sanityCheck();

	void applyClosureOperations();

	void prepareForRemove(boolean useWeqGpa);

	Set<ELEM> removeElementAndDependents(ELEM elem, Set<ELEM> elementsToRemove, Map<ELEM, ELEM> nodeToReplacementNode,
			boolean useWeqGpa);

	Object getElementCurrentlyBeingRemoved();

	void setElementCurrentlyBeingRemoved(RemoveCcElement<ELEM> re);

	boolean assertSimpleElementIsFullyRemoved(ELEM elem);

	boolean isDebugMode();

	ILogger getLogger();

	EqualityStatus getEqualityStatus(ELEM key, ELEM value);

//	boolean areEqual(ELEM key, ELEM value);

}
