package de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;

public class RemoveCcElement<ELEM extends ICongruenceClosureElement<ELEM>> //implements IRemovalInfo<ELEM> {
		implements IRemovalInfo<ELEM>, IRestoreNodesBeforeRemove<ELEM> {

	private final ELEM mElem;
	private final boolean mIntroduceNewNodes;

	private final boolean mMadeChanges;
	private Set<ELEM> mElementsToRemove;
	private final Set<ELEM> mElementsAlreadyRemoved = new HashSet<>();

	private final Set<ELEM> mAddedNodes;
	private boolean mDidRemoval = false;
	private CongruenceClosure<ELEM> mElementContainer;

	public RemoveCcElement(final CongruenceClosure<ELEM> elementContainer, final ELEM elem,
			final boolean introduceNewNodes, final boolean useWeqGpa) {
		assert !elem.isFunctionApplication() : "unexpected..";

		if (elementContainer.isInconsistent()) {
			throw new IllegalStateException();
		}

		if (elementContainer.isDebugMode()) {
			elementContainer.getLogger().debug("RemoveElement CC " + hashCode() + " : removing " + elem + " from " +
				elementContainer.hashCode());
		}

		if (!elementContainer.hasElement(elem)) {
			mElem = null;
			mMadeChanges = false;
			mAddedNodes = Collections.emptySet();
			mIntroduceNewNodes = false;
			mDidRemoval = true;
			return;
		}

		mElementContainer = elementContainer;
		mElem = elem;
		mIntroduceNewNodes = introduceNewNodes;
		mMadeChanges = false;

		mAddedNodes = mIntroduceNewNodes ? new HashSet<>() : null;
	}

	public Set<ELEM> getAddedNodes() {
		assert mDidRemoval;
		return mAddedNodes;
	}

	@Override
	public Collection<ELEM> getAlreadyRemovedElements() {
		return mElementsAlreadyRemoved;
	}

	public void doRemoval() {
		assert !mDidRemoval;
		{
			final Set<ELEM> elementsToRemove = mElementContainer.collectElementsToRemove(mElem);
			mElementsToRemove = Collections.unmodifiableSet(elementsToRemove);
		}

		assert mElementsToRemove.stream().allMatch(e -> CongruenceClosure.dependsOnAny(e, Collections.singleton(mElem)));

		/**
		 * Map in which try to collect a perfect replacement for each element that is to be removed.
		 * This map is updated through "getOtherEquivalenceMemeber", for already existing nodes,
		 *  and through getNodesToIntroducebeforeRemoval, for newly introduced equivalents.
		 *
		 * Each replacement node must be equivalent to its original node in mElementContainer.
		 *
		 * We will ensure that if the original node was a representative of an equivalence class, the replacement node
		 * will be the new representative in the equivalence class.
		 *
		 * Note that this map only needs to keep some equivalent element for each removed one (if possible). That needs
		 * to be the one that will be the new representative of the removed element's equivalence class, i.e., all the
		 * constraints that held for the removed element need to hold for its replacement.
		 * Preserving information through adding nodes is only partially related to this map.
		 */
		final Map<ELEM, ELEM> nodeToReplacementNode = new HashMap<>();

		for (final ELEM elemToRemove : mElementsToRemove) {
			final ELEM otherEqClassMember =
					mElementContainer.getOtherEquivalenceClassMember(elemToRemove, mElementsToRemove);
			if (otherEqClassMember == null) {
				continue;
			}
			nodeToReplacementNode.put(elemToRemove, otherEqClassMember);
		}
		assert DataStructureUtils.intersection(new HashSet<>(nodeToReplacementNode.values()), mElementsToRemove)
			.isEmpty();
		assert nodeAndReplacementAreEquivalent(nodeToReplacementNode, mElementContainer);

		assert !mElementContainer.isInconsistent();


		boolean becameInconsistentWhenAddingANode = false;
		becameInconsistentWhenAddingANode = addNodesToKeepInformation(this, mElementsToRemove, nodeToReplacementNode);
		if (becameInconsistentWhenAddingANode) {
			assert mElementContainer.isInconsistent();
			mDidRemoval = true;
			return;
		}

		assert nodeAndReplacementAreEquivalent(nodeToReplacementNode, mElementContainer);
		assert !mElementContainer.isInconsistent();

		assert !mElementContainer.isInconsistent();
		if (mElementContainer.isInconsistent()) {
			return;
		}

//		// (for instance:) prepare weq graph by conjoining edge labels with the current gpa
//		mElementContainer.prepareForRemove(mUseWeqGpa);

		if (!CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_1) {
			assert mElementContainer.sanityCheck();
		}

		mElementContainer.removeElements(mElementsToRemove, nodeToReplacementNode);

		if (!CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_1) {
			assert mElementContainer.sanityCheck();
		}

//		mElementContainer.applyClosureOperations();

		if (mElementContainer.isDebugMode() && mElementContainer.isInconsistent()) {
			mElementContainer.getLogger().debug("RemoveElement: " + mElementContainer.hashCode() +
					" became inconsistent during closure operation");
		}

		mDidRemoval = true;
		if (!CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_1) {
			assert mElementContainer.sanityCheck();
		}

		if (mElementContainer.isDebugMode()) {
			mElementContainer.getLogger().debug("RemoveElement " + hashCode() + " finished normally");
		}
	}


	private boolean nodeAndReplacementAreEquivalent(final Map<ELEM, ELEM> nodeToReplacementNode,
			final CongruenceClosure<ELEM> elementContainer) {
		for (final Entry<ELEM, ELEM> en : nodeToReplacementNode.entrySet()) {
			if (elementContainer.getEqualityStatus(en.getKey(), en.getValue()) != EqualityStatus.EQUAL) {
				assert false;
				return false;
			}
		}
		return true;
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> boolean
			addNodesToKeepInformation(final IRestoreNodesBeforeRemove<ELEM> rce, final Set<ELEM> elementsToRemove,
					final Map<ELEM, ELEM> nodeToReplacementNode) {
		if (!rce.isIntroduceNewNodes()) {
			return false;
		}
		while (true) {
			final Set<ELEM> nodesToAdd = new HashSet<>();

			for (final ELEM elemToRemove : elementsToRemove) {
				if (elemToRemove.isFunctionApplication() && rce.getElementContainer().isConstrained(elemToRemove)) {
					// we don't have a replacement, but we want one, try if we can get one
					final Set<ELEM> nodes = rce.getElementContainer().getNodesToIntroduceBeforeRemoval(elemToRemove,
							elementsToRemove, nodeToReplacementNode);

					nodesToAdd.addAll(nodes);
				}
			}

			assert nodesToAdd.stream().allMatch(e -> !CongruenceClosure.dependsOnAny(e,
					Collections.singleton(rce.getElem())));
			assert nodesToAdd.stream().allMatch(n -> !rce.getElementContainer().hasElement(n));
			if (!CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_1) {
				assert rce.getElementContainer().sanityCheck();
			}

			if (nodesToAdd.isEmpty()) {
				break;
			}

			if (rce.getElementContainer().isDebugMode()) {
				rce.getElementContainer().getLogger().debug("RemoveElement: adding nodes " + nodesToAdd);
			}

			// add proxy elements
			for (final ELEM proxyElem : nodesToAdd) {
				if (rce.getElementContainer().isDebugMode()) {
					rce.getElementContainer().getLogger().debug("RemoveElement: adding element " + proxyElem + " to " +
							rce.getElementContainer().hashCode() + " because it was added in weq graph label");
				}

				rce.getElementContainer().addElement(proxyElem, true);

				if (rce.getElementContainer().isInconsistent()) {
					// Cc became inconsistent through adding proxyElem --> nothing more to do
					if (rce.getElementContainer().isDebugMode()) {
						rce.getElementContainer().getLogger().debug("RemoveElement: " +
								rce.getElementContainer().hashCode() +
								" became inconsistent when adding" + proxyElem);
					}
					return true;
				}

				if (!CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_1) {
					assert rce.getElementContainer().sanityCheck();
				}
			}

			if (rce.isIntroduceNewNodes()) {
				rce.registerAddedNodes(nodesToAdd);
			}
		}
		return false;
	}

	public boolean madeChanges() {
		assert mDidRemoval;
		return mMadeChanges;
	}

	@Override
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
			final CongruenceClosure<ELEM> cc, final ELEM elem) {
		removeSimpleElement(cc, elem, true, CcSettings.MEET_WITH_WEQ_CC);
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> void removeSimpleElementDontIntroduceNewNodes(
			final CongruenceClosure<ELEM> cc, final ELEM elem) {
		removeSimpleElement(cc, elem, false, false);
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>>
			Set<ELEM> removeSimpleElementDontUseWeqGpaTrackAddedNodes(final CongruenceClosure<ELEM> cc,
					final ELEM elem) {
		return removeSimpleElement(cc, elem, true, false).getAddedNodes();
	}

	private static <ELEM extends ICongruenceClosureElement<ELEM>> RemoveCcElement<ELEM> removeSimpleElement(
			final CongruenceClosure<ELEM> cc, final ELEM elem, final boolean introduceNewNodes,
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

		cc.setElementCurrentlyBeingRemoved(re);

		re.doRemoval();
		assert cc.assertSimpleElementIsFullyRemoved(elem);

		if (!CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_1) {
			assert cc.sanityCheck();
		}

		cc.setElementCurrentlyBeingRemoved(null);

		assert cc.assertSimpleElementIsFullyRemoved(elem);
		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_2 || cc.sanityCheck();
		return re;
	}

	@Override
	public boolean isIntroduceNewNodes() {
		return mIntroduceNewNodes;
	}

	@Override
	public ELEM getElem() {
		return mElem;
	}

	@Override
	public ICongruenceClosure<ELEM> getElementContainer() {
		return mElementContainer;
	}

	@Override
	public void registerAddedNodes(final Set<ELEM> nodesToAdd) {
		mAddedNodes.addAll(nodesToAdd);
	}

}
