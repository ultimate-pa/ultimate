package de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure;

import java.util.Set;

public interface IRestoreNodesBeforeRemove<ELEM extends ICongruenceClosureElement<ELEM>> {

	boolean isIntroduceNewNodes();

	ELEM getElem();

//	IRestoreNodesBeforeRemove<ELEM> getElementContainer();
	ICongruenceClosure<ELEM> getElementContainer();

//	boolean hasElement(ELEM n);

//	boolean sanityCheck();

//	boolean isDebugMode();

//	ILogger getLogger();

//	void addElement(ELEM proxyElem, boolean b);

//	boolean isInconsistent();

	void registerAddedNodes(Set<ELEM> nodesToAdd);

//	boolean isConstrained(ELEM elemToRemove);

//	Set<ELEM> getNodesToIntroduceBeforeRemoval(ELEM elemToRemove, Set<ELEM> elementsToRemove,
//			Map<ELEM, ELEM> nodeToReplacementNode);

}
