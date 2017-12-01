package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure.CcSettings;

public class RemoveCcElement<ELEM extends ICongruenceClosureElement<ELEM>> {

	private final ELEM mElem;
	private final boolean mIntroduceNewNodes;
	private final boolean mUseWeqGpa;

	private final boolean mMadeChanges;
	private Set<ELEM> mElementsToRemove;
	private final Set<ELEM> mElementsAlreadyRemoved = new HashSet<>();

	private final Set<ELEM> mAddedNodes;
	private boolean mDidRemoval = false;
	private ICcRemoveElement<ELEM> mElementContainer;

	public RemoveCcElement(final ICcRemoveElement<ELEM> elementContainer, final ELEM elem,
			final boolean introduceNewNodes, final boolean useWeqGpa) {
		assert !elem.isFunctionApplication() : "unexpected..";

		if (elementContainer.isInconsistent()) {
			throw new IllegalStateException();
		}

		if (elementContainer.isDebugMode()) {
			elementContainer.getLogger().debug("RemoveElement " + hashCode() + " : removing " + elem + " from " +
				elementContainer.hashCode());
		}

		if (!elementContainer.hasElement(elem)) {
			mElem = null;
			mMadeChanges = false;
			mAddedNodes = Collections.emptySet();
			mIntroduceNewNodes = false;
			mUseWeqGpa = false;
			mDidRemoval = true;
			return;
		}

		mElementContainer = elementContainer;
		mElem = elem;
		mIntroduceNewNodes = introduceNewNodes;
		mUseWeqGpa = useWeqGpa;
		mMadeChanges = false;

		mAddedNodes = mUseWeqGpa && mIntroduceNewNodes ? null : new HashSet<>();
	}

	public Set<ELEM> getAddedNodes() {
		assert !mUseWeqGpa : "currently the only case we need this, right?";
		assert mDidRemoval;
		return mAddedNodes;
	}

	public Collection<ELEM> getAlreadyRemovedElements() {
		return mElementsAlreadyRemoved;
	}

	public void doRemoval() {
		assert !mDidRemoval;
		final Set<ELEM> elementsToRemove = mElementContainer.collectElementsToRemove(mElem);
		mElementsToRemove = Collections.unmodifiableSet(elementsToRemove);

		assert elementsToRemove.stream().allMatch(e -> CongruenceClosure.dependsOnAny(e, Collections.singleton(mElem)));

		/**
		 * Map in which try to collect a perfect replacement for each element that is to be removed.
		 * This map is updated through "getOtherEquivalenceMemeber", for already existing nodes,
		 *  and through getNodesToIntroducebeforeRemoval, for newly introduced equivalents.
		 */
		final Map<ELEM, ELEM> nodeToReplacementNode = new HashMap<>();

		for (final ELEM elemToRemove : elementsToRemove) {
			nodeToReplacementNode.put(elemToRemove,
					mElementContainer.getOtherEquivalenceClassMember(elemToRemove, elementsToRemove));
		}
		assert DataStructureUtils.intersection(new HashSet<>(nodeToReplacementNode.values()), elementsToRemove)
			.isEmpty();

		assert !mElementContainer.isInconsistent();

		while (true) {
			if (!mIntroduceNewNodes) {
				break;
			}
			final Set<ELEM> nodesToAdd = new HashSet<>();

			for (final ELEM elemToRemove : elementsToRemove) {
				if (elemToRemove.isFunctionApplication() && mElementContainer.isConstrained(elemToRemove)) {
					// we don't have a replacement, but we want one, try if we can get one
					final Set<ELEM> replacementNodes =
							mElementContainer.getNodesToIntroduceBeforeRemoval(elemToRemove, nodeToReplacementNode);
					nodesToAdd.addAll(replacementNodes);
				}
			}

			assert nodesToAdd.stream().allMatch(e -> !CongruenceClosure.dependsOnAny(e, Collections.singleton(mElem)));
			assert nodesToAdd.stream().allMatch(n -> !mElementContainer.hasElement(n));
			assert mElementContainer.sanityCheck();

			if (nodesToAdd.isEmpty()) {
				break;
			}

			if (mElementContainer.isDebugMode()) {
				mElementContainer.getLogger().debug("RemoveElement: adding nodes " + nodesToAdd);
			}

			// add proxy elements
			for (final ELEM proxyElem : nodesToAdd) {
				if (mElementContainer.isDebugMode()) {
					mElementContainer.getLogger().debug("RemoveElement: adding element " + proxyElem + " to " +
							mElementContainer.hashCode() + " because it was added in weq graph label");
				}

				mElementContainer.addElementRec(proxyElem);

				if (mElementContainer.isInconsistent()) {
					// Cc became inconsistent through adding proxyElem --> nothing more to do
					if (mElementContainer.isDebugMode()) {
						mElementContainer.getLogger().debug("RemoveElement: " + mElementContainer.hashCode() +
								" became inconsistent when adding" + proxyElem);
					}
					mDidRemoval = true;
					return;
				}

				assert mElementContainer.sanityCheck();
			}

			if (mIntroduceNewNodes && !mUseWeqGpa) {
				mAddedNodes.addAll(nodesToAdd);
			}
		}

		assert !mElementContainer.isInconsistent();

		mElementContainer.applyClosureOperations();

		assert !mElementContainer.isInconsistent();
		if (mElementContainer.isInconsistent()) {
			return;
		}

		// (for instance:) prepare weq graph by conjoining edge labels with the current gpa
		mElementContainer.prepareForRemove(mUseWeqGpa);

		final Set<ELEM> nodesAddedInLabels = mElementContainer.removeElementAndDependents(mElem, elementsToRemove,
				nodeToReplacementNode, mUseWeqGpa);

		// the edge labels may have added nodes when projecting something --> add them to the gpa
		for (final ELEM nail : nodesAddedInLabels) {
			mElementContainer.addElementRec(nail);

			if (mElementContainer.isInconsistent()) {
				// Cc became inconsistent through adding proxyElem --> nothing more to do
				if (mElementContainer.isDebugMode()) {
					mElementContainer.getLogger().debug("RemoveElement: " + mElementContainer.hashCode() +
							" became inconsistent when adding" + nail);
				}
				mDidRemoval = true;
				return;
			}
		}
		assert mElementContainer.sanityCheck();
		mElementContainer.applyClosureOperations();

		if (mElementContainer.isDebugMode() && mElementContainer.isInconsistent()) {
			mElementContainer.getLogger().debug("RemoveElement: " + mElementContainer.hashCode() +
					" became inconsistent during closure operation");
		}



		mDidRemoval = true;
		assert mElementContainer.sanityCheck();

		if (mElementContainer.isDebugMode()) {
			mElementContainer.getLogger().debug("RemoveElement " + hashCode() + " finished normally");
		}
	}

	public boolean madeChanges() {
		assert mDidRemoval;
		return mMadeChanges;
	}

	public Set<ELEM> getRemovedElements() {
		return mElementsToRemove;
	}

	@Override
	public String toString() {
		return mElementsToRemove.toString();
	}

	/**
	 * Remove a simple element, i.e., an element that is not a function application.
	 *
	 * During removal, CongruenceClosure attempts to add nodes in order to retain constraints that follow from the
	 * constraint but were not explicit before.
	 *
	 * @param elem
	 * @param preferredReplacements
	 * @return
	 */
	public static <ELEM extends ICongruenceClosureElement<ELEM>> void removeSimpleElement(
			final ICcRemoveElement<ELEM> cc, final ELEM elem) {
		removeSimpleElement(cc, elem, true, CcSettings.MEET_WITH_WEQ_CC);
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> void removeSimpleElementDontIntroduceNewNodes(
			final ICcRemoveElement<ELEM> cc, final ELEM elem) {
		removeSimpleElement(cc, elem, false, false);
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>>
			Set<ELEM> removeSimpleElementDontUseWeqGpaTrackAddedNodes(final ICcRemoveElement<ELEM> cc,
					final ELEM elem) {
		return removeSimpleElement(cc, elem, true, false).getAddedNodes();
	}

	private static <ELEM extends ICongruenceClosureElement<ELEM>> RemoveCcElement<ELEM> removeSimpleElement(
			final ICcRemoveElement<ELEM> cc, final ELEM elem, final boolean introduceNewNodes,
			final boolean useWeqGpa) {
		if (elem.isFunctionApplication()) {
			throw new IllegalArgumentException();
		}
		if (cc.isInconsistent()) {
			throw new IllegalStateException();
		}

		assert cc.getElementCurrentlyBeingRemoved() == null;
		final RemoveCcElement<ELEM> re = new RemoveCcElement<>(cc, elem, introduceNewNodes, useWeqGpa);

		if (!cc.hasElement(elem)) {
			// re recognizes this case -- no need to execute doRemoval
			assert !re.madeChanges();
			assert re.getAddedNodes().isEmpty();
			return re;
		}

		//		mElementCurrentlyBeingRemoved = re;
		cc.setElementCurrentlyBeingRemoved(re);

		re.doRemoval();
		assert cc.assertSimpleElementIsFullyRemoved(elem);
		assert cc.sanityCheck();

		//		mElementCurrentlyBeingRemoved = null;
		cc.setElementCurrentlyBeingRemoved(null);

		assert cc.assertSimpleElementIsFullyRemoved(elem);
		assert cc.sanityCheck();
		return re;
	}

}