package de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CcSettings;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.IRemovalInfo;

public class RemoveWeqCcElement<NODE extends IEqNodeIdentifier<NODE>> implements IRemovalInfo<NODE> {

	private final NODE mElem;
	private final boolean mIntroduceNewNodes;
	private final boolean mUseWeqGpa;

	private final boolean mMadeChanges;
	private Set<NODE> mElementsToRemove;
	private final Set<NODE> mElementsAlreadyRemoved = new HashSet<>();

	private final Set<NODE> mAddedNodes;
	private boolean mDidRemoval = false;
	private WeqCongruenceClosure<NODE> mWeqCc;

	public RemoveWeqCcElement(final WeqCongruenceClosure<NODE> elementContainer, final NODE elem,
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

		mWeqCc = elementContainer;
		mElem = elem;
		mIntroduceNewNodes = introduceNewNodes;
		mUseWeqGpa = useWeqGpa;
		mMadeChanges = false;

		mAddedNodes = mUseWeqGpa && mIntroduceNewNodes ? null : new HashSet<>();
	}

	public Set<NODE> getAddedNodes() {
		assert !mUseWeqGpa : "currently the only case we need this, right?";
		assert mDidRemoval;
		return mAddedNodes;
	}

	@Override
	public Collection<NODE> getAlreadyRemovedElements() {
		return mElementsAlreadyRemoved;
	}

	public void doRemoval() {
		assert !mDidRemoval;
		final Set<NODE> elementsToRemove = mWeqCc.collectElementsToRemove(mElem);
		mElementsToRemove = Collections.unmodifiableSet(elementsToRemove);

		assert elementsToRemove.stream().allMatch(e -> CongruenceClosure.dependsOnAny(e, Collections.singleton(mElem)));

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
		final Map<NODE, NODE> nodeToReplacementNode = new HashMap<>();

		for (final NODE elemToRemove : elementsToRemove) {
			final NODE otherEqClassMember =
					mWeqCc.getOtherEquivalenceClassMember(elemToRemove, elementsToRemove);
			if (otherEqClassMember == null) {
				continue;
			}
			nodeToReplacementNode.put(elemToRemove, otherEqClassMember);
		}
		assert DataStructureUtils.intersection(new HashSet<>(nodeToReplacementNode.values()), elementsToRemove)
			.isEmpty();
		assert nodeAndReplacementAreEquivalent(nodeToReplacementNode, mWeqCc);

		assert !mWeqCc.isInconsistent();


		boolean becameInconsistentWhenAddingANode = false;
		becameInconsistentWhenAddingANode = addNodesToKeepInformation(elementsToRemove, nodeToReplacementNode);
		if (becameInconsistentWhenAddingANode) {
			assert mWeqCc.isInconsistent();
			mDidRemoval = true;
			return;
		}

		assert nodeAndReplacementAreEquivalent(nodeToReplacementNode, mWeqCc);
		assert !mWeqCc.isInconsistent();

		if (!CcSettings.DELAY_EXT_AND_DELTA_CLOSURE) {
			mWeqCc.extAndTriangleClosure();
		}

		assert !mWeqCc.isInconsistent();
		if (mWeqCc.isInconsistent()) {
			return;
		}

		// (for instance:) prepare weq graph by conjoining edge labels with the current gpa
		mWeqCc.fatten(mUseWeqGpa);

		final Set<NODE> nodesAddedInLabels = mWeqCc.removeElementAndDependents(mElem, elementsToRemove,
					nodeToReplacementNode, mUseWeqGpa);

		mWeqCc.thin();

		// the edge labels may have added nodes when projecting something --> add them to the gpa
		for (final NODE nail : nodesAddedInLabels) {
			mWeqCc.addElementRec(nail);

			if (mWeqCc.isInconsistent()) {
				// Cc became inconsistent through adding proxyElem --> nothing more to do
				if (mWeqCc.isDebugMode()) {
					mWeqCc.getLogger().debug("RemoveElement: " + mWeqCc.hashCode() +
							" became inconsistent when adding" + nail);
				}
				mDidRemoval = true;
				return;
			}
		}
		assert mWeqCc.sanityCheck();
		mWeqCc.extAndTriangleClosure();

		if (mWeqCc.isDebugMode() && mWeqCc.isInconsistent()) {
			mWeqCc.getLogger().debug("RemoveElement: " + mWeqCc.hashCode() +
					" became inconsistent during closure operation");
		}



		mDidRemoval = true;
		assert mWeqCc.sanityCheck();

		if (mWeqCc.isDebugMode()) {
			mWeqCc.getLogger().debug("RemoveElement " + hashCode() + " finished normally");
		}
	}


	private boolean nodeAndReplacementAreEquivalent(final Map<NODE, NODE> nodeToReplacementNode,
			final WeqCongruenceClosure<NODE> elementContainer) {
		for (final Entry<NODE, NODE> en : nodeToReplacementNode.entrySet()) {
			if (elementContainer.getEqualityStatus(en.getKey(), en.getValue()) != EqualityStatus.EQUAL) {
				assert false;
				return false;
			}
		}
		return true;
	}

	private boolean addNodesToKeepInformation(final Set<NODE> elementsToRemove,
			final Map<NODE, NODE> nodeToReplacementNode) {
		if (!mIntroduceNewNodes) {
			return false;
		}
		while (true) {
			final Set<NODE> nodesToAdd = new HashSet<>();

			for (final NODE elemToRemove : elementsToRemove) {
				if (elemToRemove.isFunctionApplication() && mWeqCc.isConstrained(elemToRemove)) {
					// we don't have a replacement, but we want one, try if we can get one
					final Set<NODE> nodes = mWeqCc.getNodesToIntroduceBeforeRemoval(elemToRemove,
							elementsToRemove, nodeToReplacementNode);

					nodesToAdd.addAll(nodes);
				}
			}

			assert nodesToAdd.stream().allMatch(e -> !CongruenceClosure.dependsOnAny(e, Collections.singleton(mElem)));
			assert nodesToAdd.stream().allMatch(n -> !mWeqCc.hasElement(n));
			assert mWeqCc.sanityCheck();

			if (nodesToAdd.isEmpty()) {
				break;
			}

			if (mWeqCc.isDebugMode()) {
				mWeqCc.getLogger().debug("RemoveElement: adding nodes " + nodesToAdd);
			}

			// add proxy elements
			for (final NODE proxyElem : nodesToAdd) {
				if (mWeqCc.isDebugMode()) {
					mWeqCc.getLogger().debug("RemoveElement: adding element " + proxyElem + " to " +
							mWeqCc.hashCode() + " because it was added in weq graph label");
				}

				mWeqCc.addElementRec(proxyElem);

				if (mWeqCc.isInconsistent()) {
					// Cc became inconsistent through adding proxyElem --> nothing more to do
					if (mWeqCc.isDebugMode()) {
						mWeqCc.getLogger().debug("RemoveElement: " + mWeqCc.hashCode() +
								" became inconsistent when adding" + proxyElem);
					}
					return true;
				}

				assert mWeqCc.sanityCheck();
			}

			if (mIntroduceNewNodes && !mUseWeqGpa) {
				mAddedNodes.addAll(nodesToAdd);
			}
		}
		return false;
	}

	public boolean madeChanges() {
		assert mDidRemoval;
		return mMadeChanges;
	}

	@Override
	public Set<NODE> getRemovedElements() {
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
	public static <NODE extends IEqNodeIdentifier<NODE>> void removeSimpleElement(
			final WeqCongruenceClosure<NODE> cc, final NODE elem) {
		removeSimpleElement(cc, elem, true, WeqSettings.USE_FULL_WEQCC_DURING_PROJECTAWAY);
	}

	private static <NODE extends IEqNodeIdentifier<NODE>> RemoveWeqCcElement<NODE> removeSimpleElement(
			final WeqCongruenceClosure<NODE> cc, final NODE elem, final boolean introduceNewNodes,
			final boolean useWeqGpa) {
		if (elem.isFunctionApplication()) {
			throw new IllegalArgumentException();
		}
		if (cc.isInconsistent()) {
			throw new IllegalStateException();
		}

		assert cc.getElementCurrentlyBeingRemoved() == null;
		final RemoveWeqCcElement<NODE> re = new RemoveWeqCcElement<>(cc, elem, introduceNewNodes, useWeqGpa);

		if (!cc.hasElement(elem)) {
			// re recognizes this case -- no need to execute doRemoval
			assert !re.madeChanges();
			assert re.getAddedNodes().isEmpty();
			return re;
		}

		cc.setElementCurrentlyBeingRemoved(re);

		re.doRemoval();
		assert cc.assertSimpleElementIsFullyRemoved(elem);
		if (WeqSettings.SANITYCHECK_FINE_GRAINED) {
			assert cc.sanityCheck();
		}

		cc.setElementCurrentlyBeingRemoved(null);

		assert cc.assertSimpleElementIsFullyRemoved(elem);
		assert cc.sanityCheck();
		return re;
	}

	public static <NODE extends IEqNodeIdentifier<NODE>> Set<NODE> removeSimpleElementDontUseWeqGpaTrackAddedNodes(
			final WeqCongruenceClosure<NODE> lab, final NODE elem) {
		final RemoveWeqCcElement<NODE> re =
				removeSimpleElement(lab, elem, true, false);
		return re.getAddedNodes();
	}

}
