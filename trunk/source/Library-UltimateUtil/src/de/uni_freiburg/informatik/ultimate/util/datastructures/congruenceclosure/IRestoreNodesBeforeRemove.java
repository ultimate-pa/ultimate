package de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure;

import java.util.Set;

/**
 * Introduced to have only one version of the method {@link RemoveCcElement#addNodesToKeepInformation}.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ELEM>
 */
public interface IRestoreNodesBeforeRemove<ELEM extends ICongruenceClosureElement<ELEM>> {

	boolean isIntroduceNewNodes();

	ELEM getElem();

	IElementRemovalTarget<ELEM> getElementContainer();

	void registerAddedNodes(Set<ELEM> nodesToAdd);

}
