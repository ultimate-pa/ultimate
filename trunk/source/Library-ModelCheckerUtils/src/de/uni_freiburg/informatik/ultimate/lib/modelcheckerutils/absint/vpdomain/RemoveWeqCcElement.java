package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain;

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
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.IElementRemovalTarget;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.IRemovalInfo;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.IRestoreNodesBeforeRemove;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.RemoveCcElement;

public class RemoveWeqCcElement<NODE extends IEqNodeIdentifier<NODE>>
		implements IRemovalInfo<NODE>, IRestoreNodesBeforeRemove<NODE> {

	private final NODE mElem;
	private final boolean mIntroduceNewNodes;
//	private final boolean mUseWeqGpa;

	private final boolean mMadeChanges;
	private Set<NODE> mElementsToRemove;
	private final Set<NODE> mElementsAlreadyRemoved = new HashSet<>();

	private final Set<NODE> mAddedNodes;
	private boolean mDidRemoval = false;
	private WeqCongruenceClosure<NODE> mWeqCc;

	public RemoveWeqCcElement(final WeqCongruenceClosure<NODE> elementContainer, final NODE elem,
			final boolean introduceNewNodes) {
		assert !elem.isFunctionApplication() : "unexpected..";

		if (elementContainer.isInconsistent(false)) {
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
//			mUseWeqGpa = false;
			mDidRemoval = true;
			return;
		}

		mWeqCc = elementContainer;
		mElem = elem;
		mIntroduceNewNodes = introduceNewNodes;
//		mUseWeqGpa = useWeqGpa;
		mMadeChanges = false;

		mAddedNodes = !mIntroduceNewNodes ? null : new HashSet<>();
	}

	public Set<NODE> getAddedNodes() {
//		assert !mUseWeqGpa : "currently the only case we need this, right?";
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

		assert !mWeqCc.isInconsistent(false);


		boolean becameInconsistentWhenAddingANode = false;
		becameInconsistentWhenAddingANode =
				RemoveCcElement.addNodesToKeepInformation(this, elementsToRemove, nodeToReplacementNode);

		// add constraints that were made possible by adding nodes
		mWeqCc.reportAllConstraintsFromWeqGraph(false);
		// tried (14/08/2018): induces massive (!) performance loss, consequences for precision unclear
//		mWeqCc.extAndTriangleClosure(true);
//		mWeqCc.getManager().closeIfNecessary(mWeqCc);

		if (becameInconsistentWhenAddingANode) {
			assert mWeqCc.isInconsistent(false);
			mDidRemoval = true;
			return;
		}

		assert nodeAndReplacementAreEquivalent(nodeToReplacementNode, mWeqCc);
		assert !mWeqCc.isInconsistent(false);

		if (!CcSettings.DELAY_EXT_AND_DELTA_CLOSURE) {
			mWeqCc.extAndTriangleClosure(false);
			// unnecessary, as we call closure later
//		} else {
//			mWeqCc.mIsClosed = false;
		}

		assert !mWeqCc.isInconsistent(false);

		// (for instance:) prepare weq graph by conjoining edge labels with the current gpa
		mWeqCc.fatten();
//		assert !mUseWeqGpa || mWeqCc.assertAllEdgeLabelsHaveWeqFatFlagSet();

		// TODO: should we do a full closure here (like when freezing??)

		final Set<NODE> nodesAddedInLabels = mWeqCc.removeElementAndDependents(mElem, elementsToRemove,
					nodeToReplacementNode);

		mWeqCc.thin();

		if (!mWeqCc.getManager().getSettings().omitSanitycheckFineGrained1()) {
			assert mWeqCc.getCongruenceClosure().sanityCheck();
		}

		// the edge labels may have added nodes when projecting something --> add them to the gpa
		for (final NODE nail : nodesAddedInLabels) {
			mWeqCc.addElementRec(nail);

			if (mWeqCc.isInconsistent(false)) {
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
		mWeqCc.extAndTriangleClosure(false);

		if (mWeqCc.isDebugMode() && mWeqCc.isInconsistent(false)) {
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
		removeSimpleElement(cc, elem, true);
	}

	private static <NODE extends IEqNodeIdentifier<NODE>> RemoveWeqCcElement<NODE> removeSimpleElement(
			final WeqCongruenceClosure<NODE> cc, final NODE elem, final boolean introduceNewNodes) {
		if (elem.isFunctionApplication()) {
			throw new IllegalArgumentException();
		}
		if (cc.isInconsistent(false)) {
			throw new IllegalStateException();
		}

		assert cc.getElementCurrentlyBeingRemoved() == null;
		final RemoveWeqCcElement<NODE> re = new RemoveWeqCcElement<>(cc, elem, introduceNewNodes);

		if (!cc.hasElement(elem)) {
			// re recognizes this case -- no need to execute doRemoval
			assert !re.madeChanges();
			assert re.getAddedNodes().isEmpty();
			return re;
		}

		cc.setElementCurrentlyBeingRemoved(re);

		re.doRemoval();
		assert cc.assertSimpleElementIsFullyRemoved(elem);
		if (!cc.getManager().getSettings().omitSanitycheckFineGrained1()) {
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
				removeSimpleElement(lab, elem, true);
		return re.getAddedNodes();
	}

	@Override
	public boolean isIntroduceNewNodes() {
		return mIntroduceNewNodes;
	}

	@Override
	public NODE getElem() {
		return mElem;
	}

	@Override
	public IElementRemovalTarget<NODE> getElementContainer() {
		return mWeqCc;
	}

	@Override
	public void registerAddedNodes(final Set<NODE> nodesToAdd) {
		mAddedNodes.addAll(nodesToAdd);
	}

}
