/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Implementation of the congruence closure algorithm and data structure. Builds
 * upon ThreeValuedEquivalenceRelation, and also uses a three valued logic
 * (equal, not_equal, unknown).
 * <p>
 * Provides operations for adding equality and disequality constraints both on
 * elements and functions. Automatically closes under the congruence axioms with
 * respect to all the known elements. Can propagate equalities and
 * disequalities.
 * <p>
 * Requires the ELEM type to implement the ICongruenceClosureElement interface.
 * It is recommended to use a factory for constructing ELEM objects that extends
 * AbstractCCElementFactory.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ELEM>
 *            The element type. Elements correspond to the "nodes" or terms in
 *            standard congruence closure terminology. Elements can be constants
 *            or function applications.
 */
public class CongruenceClosure<ELEM extends ICongruenceClosureElement<ELEM>>
		implements ICongruenceClosure<ELEM> {

	protected final ThreeValuedEquivalenceRelation<ELEM> mElementTVER;

	private final CcAuxData<ELEM> mAuxData;

	protected final CongruenceClosure<ELEM>.FuncAppTreeAuxData mFaAuxData;

	protected final Collection<ELEM> mAllLiterals;

	protected boolean mIsFrozen = false;

	boolean mConstructorInitializationPhase = false;

	/**
	 * Store which element we are currently in the process of removing (a remove can trigger deep recursive calls, and
	 *  some need to know this. Also sanity checks may be done more precisely when we know this)
	 */
	protected IRemovalInfo<ELEM> mElementCurrentlyBeingRemoved;

	private IRemovalInfo<ELEM> mExternalRemovalInfo;

	private final CcManager<ELEM> mManager;

	/**
	 * Constructs CongruenceClosure instance without any equalities or
	 * disequalities.
	 * @param manager
	 *
	 * @param logger a logger, can be null (isDebug will return false, then)
	 */
	CongruenceClosure(final CcManager<ELEM> manager) {
		mElementTVER = new ThreeValuedEquivalenceRelation<>(CongruenceClosure::literalComparator);
		mAuxData = new CcAuxData<ELEM>(this);
		mFaAuxData = new FuncAppTreeAuxData();
		mAllLiterals = new HashSet<>();
		mManager = manager;
	}

	/**
	 * Constructs CongruenceClosure instance that is in an inconsistent state from
	 * the beginning.
	 *
	 * @param isInconsistent dummy parameter separating this constructor from the one for the empty CongruenceClosure;
	 * 	  	must always be "true".
	 */
	CongruenceClosure(final boolean isInconsistent) {
		if (!isInconsistent) {
			throw new AssertionError("use other constructor");
		}
		mElementTVER = null;
		mAuxData = null;
		mFaAuxData = null;
		mAllLiterals = null;
		mManager = null;
	}

	/**
	 *
	 * @param logger a logger, can be null (isDebug will return false, then)
	 * @param newElemPartition
	 */
	CongruenceClosure(final CcManager<ELEM> manager,
			final ThreeValuedEquivalenceRelation<ELEM> newElemPartition) {
		mManager = manager;

		mElementTVER = newElemPartition;
		mAuxData = new CcAuxData<>(this);
		mFaAuxData = new FuncAppTreeAuxData();
		mAllLiterals = new HashSet<>();

		mConstructorInitializationPhase = true;
		// initialize the helper mappings according to mElementTVER
		for (final ELEM elem : new HashSet<>(mElementTVER.getAllElements())) {
			registerNewElement(elem);
		}
		mConstructorInitializationPhase = false;

		assert sanityCheck();
	}

	/**
	 *
	 * @param logger a logger, can be null (isDebug will return false, then)
	 * @param newElemPartition
	 * @param remInfo
	 */
	CongruenceClosure(final CcManager<ELEM> manager, final ThreeValuedEquivalenceRelation<ELEM> newElemPartition,
			final IRemovalInfo<ELEM> remInfo) {
		mElementTVER = newElemPartition;
		mAuxData = new CcAuxData<>(this);
		mFaAuxData = new FuncAppTreeAuxData();
		mAllLiterals = new HashSet<>();

		mConstructorInitializationPhase = true;
		// initialize the helper mappings according to mElementTVER
		for (final ELEM elem : new HashSet<>(mElementTVER.getAllElements())) {
			registerNewElement(elem, remInfo);
		}
		mConstructorInitializationPhase = false;
		mManager = manager;
		assert sanityCheck(remInfo);
	}

	/**
	 *
	 * @param original
	 * @param externalRemovalInfo
	 */
	CongruenceClosure(final CongruenceClosure<ELEM> original, final IRemovalInfo<ELEM> externalRemovalInfo) {
		if (original.isInconsistent()) {
			throw new IllegalArgumentException("use other constructor!");
		}
		mElementTVER = new ThreeValuedEquivalenceRelation<>(original.mElementTVER);
		mAuxData = new CcAuxData<>(this, original.getAuxData());
		mFaAuxData = new FuncAppTreeAuxData(original.mFaAuxData);
		mAllLiterals = new HashSet<>(original.mAllLiterals);
		mExternalRemovalInfo = externalRemovalInfo;
		mManager = original.mManager;
		assert sanityCheck(externalRemovalInfo); // can be violated during remove (?)
	}

	/**
	 * Copy constructor.
	 *
	 * @param original the CC to copy
	 */
	CongruenceClosure(final CongruenceClosure<ELEM> original) {
		this(original, null);
	}

	static <ELEM extends ICongruenceClosureElement<ELEM>> Integer literalComparator(final ELEM e1, final ELEM e2) {
		if (e1.isLiteral() && !e2.isLiteral()) {
			return -1;
		}
		if (e2.isLiteral() && !e1.isLiteral()) {
			return 1;
		}
		return 0;
	}

	/**
	 * Sets the flag for isFrozen() to true.
	 */
	public void freeze() {
		assert !mIsFrozen;
		mIsFrozen = true;
	}

	public boolean isFrozen() {
		return mIsFrozen;
	}

	boolean reportEquality(final ELEM elem1, final ELEM elem2) {
		final boolean result = reportEqualityRec(elem1, elem2);
		assert sanityCheck();
		return result;
	}

	public boolean reportEqualityRec(final ELEM elem1, final ELEM elem2) {
		assert !mIsFrozen;
		if (isInconsistent()) {
			throw new IllegalStateException();
		}

		boolean freshElem = false;
//		freshElem |= addElementRec(elem1);
//		freshElem |= addElementRec(elem2);
		freshElem |= mManager.addElementReportChange(this, elem1, true);
		freshElem |= mManager.addElementReportChange(this, elem2, true);
		assert assertAtMostOneLiteralPerEquivalenceClass();

		if (getEqualityStatus(elem1, elem2) == EqualityStatus.EQUAL) {
			// nothing to do
			return freshElem;
		}
		if (getEqualityStatus(elem1, elem2) == EqualityStatus.NOT_EQUAL) {
			// report it to tver so that it is in an inconsistent state
			mElementTVER.reportEquality(elem1, elem2);
			// not so nice, but needed for literals where TVER does not know they are unequal otherwise
			if (!mElementTVER.isInconsistent()) {
				mElementTVER.reportDisequality(elem1, elem2);
			}
			assert mElementTVER.isInconsistent();
			return true;
		}

		final Pair<HashRelation<ELEM, ELEM>, HashRelation<ELEM, ELEM>> propInfo = doMergeAndComputePropagations(elem1,
				elem2);
		if (propInfo == null) {
			// this became inconsistent through the merge
			return true;
		}

		doFwccAndBwccPropagationsFromMerge(propInfo);

//		assert sanityCheck();
		assert assertAtMostOneLiteralPerEquivalenceClass();
		return true;
	}

	public void doFwccAndBwccPropagationsFromMerge(
			final Pair<HashRelation<ELEM, ELEM>, HashRelation<ELEM, ELEM>> propInfo) {
		final HashRelation<ELEM, ELEM> equalitiesToPropagate = propInfo.getFirst();
		final HashRelation<ELEM, ELEM> disequalitiesToPropagate = propInfo.getSecond();
		/*
		 * (fwcc)
		 */
		for (final Entry<ELEM, ELEM> congruentParents : equalitiesToPropagate) {
			if (isInconsistent()) {
				return;
			}
			reportEqualityRec(congruentParents.getKey(), congruentParents.getValue());
		}

		/*
		 * (bwcc1), (bwcc2)  (-- they're only separate cases during reportDisequality)
		 */
		for (final Entry<ELEM, ELEM> unequalNeighborIndices : disequalitiesToPropagate) {
			if (isInconsistent()) {
				return;
			}
			reportDisequalityRec(unequalNeighborIndices.getKey(), unequalNeighborIndices.getValue());
		}
	}

	public Pair<HashRelation<ELEM, ELEM>, HashRelation<ELEM, ELEM>> doMergeAndComputePropagations(final ELEM elem1,
			final ELEM elem2) {
		final ELEM e1OldRep = mElementTVER.getRepresentative(elem1);
		final ELEM e2OldRep = mElementTVER.getRepresentative(elem2);

		/*
		 * These sets are used for bwcc propagations, there the special case for the disequalities introduced through
		 * transitivity.
		 * Should save some useless propagations, and avoid some weirdness in debugging..
		 */
		final Set<ELEM> oldUnequalRepsForElem1 = getRepresentativesUnequalTo(e1OldRep);
		final Set<ELEM> oldUnequalRepsForElem2 = getRepresentativesUnequalTo(e2OldRep);

		mElementTVER.reportEquality(elem1, elem2);
		if (mElementTVER.isInconsistent()) {
			return null;
		}

		final Pair<HashRelation<ELEM, ELEM>, HashRelation<ELEM, ELEM>> propInfo =
				getAuxData().updateAndGetPropagationsOnMerge(elem1, elem2, e1OldRep, e2OldRep,
						oldUnequalRepsForElem1, oldUnequalRepsForElem2);
		return propInfo;
	}


	public Set<ELEM> getRepresentativesUnequalTo(final ELEM rep) {
		assert isRepresentative(rep);
		final Set<ELEM> result = new HashSet<>(mElementTVER.getRepresentativesUnequalTo(rep));

		if (rep.isLiteral()) {
			for (final ELEM lit : mAllLiterals) {
				if (!lit.equals(rep)) {
					result.add(lit);
				}
			}
		}

		return result;
	}

	boolean reportDisequality(final ELEM elem1, final ELEM elem2) {
		final boolean result = reportDisequalityRec(elem1, elem2);
		assert sanityCheck();
		return result;
	}

	public boolean reportDisequalityRec(final ELEM elem1, final ELEM elem2) {
		assert !mIsFrozen;
		assert elem1.hasSameTypeAs(elem2);

		if (isInconsistent()) {
			throw new IllegalStateException();
		}

		boolean freshElem = false;
		freshElem |= mManager.addElementReportChange(this, elem1, true);
		freshElem |= mManager.addElementReportChange(this, elem2, true);

		if (!freshElem && getEqualityStatus(elem1, elem2) == EqualityStatus.NOT_EQUAL) {
			// nothing to do
			return false;
		}


		mElementTVER.reportDisequality(elem1, elem2);
		if (mElementTVER.isInconsistent()) {
			return true;
		}

		final HashRelation<ELEM, ELEM> propDeqs = getAuxData().getPropagationsOnReportDisequality(elem1, elem2);

		for (final Entry<ELEM, ELEM> deq : propDeqs) {
			reportDisequalityRec(deq.getKey(), deq.getValue());
		}

		return true;
	}

//	/**
//	 *
//	 * @param elem
//	 * @return true iff the element was not known to this CongruenceClosure before
//	 */
//	void addElement(final ELEM elem) {
//		addElementRec(elem);
//		assert sanityCheck();
//	}

	public boolean addElement(final ELEM elem, final boolean omitSanityCheck) {
		final boolean result = addElementRec(elem, null);
		assert omitSanityCheck || sanityCheck();
		return result;
	}

	private boolean addElementRec(final ELEM elem, final IRemovalInfo<ELEM> remInfo) {
		assert !mIsFrozen;
		final boolean newlyAdded = mElementTVER.addElement(elem);
		if (newlyAdded) {
			registerNewElement(elem, remInfo);
		}
//		assert sanityCheckOnlyCc();
		return newlyAdded;
	}

	/**
	 * Updates the helper mappings for ccpars, ccchildren, and function
	 * applications. When a new element is added.
	 *
	 * Assumes that the element has been added to mElementTVER by addElement(elem), but was not present before that call
	 * to addElement(..).
	 *
	 * @param elem
	 */
	private void registerNewElement(final ELEM elem) {
		registerNewElement(elem, null);
	}

	public void registerNewElement(final ELEM elem, final IRemovalInfo<ELEM> remInfo) {
		if (elem.isLiteral()) {
			mAllLiterals.add(elem);
		}

		if (elem.isDependent()) {
			for (final ELEM supp : elem.getSupportingNodes()) {
				mManager.addElement(this, supp, true, true);
				mFaAuxData.addSupportingNode(supp, elem);
			}
		}


		if (!elem.isFunctionApplication()) {
			// nothing to do
			assert mElementTVER.getRepresentative(elem) != null : "this method assumes that elem has been added "
					+ "already";
//			assert sanityCheck();
			return;
		}


		if (remInfo == null) {
			// "fast track"
			mFaAuxData.addAfParent(elem.getAppliedFunction(), elem);
			mFaAuxData.addArgParent(elem.getArgument(), elem);
		} else {
			if (!remInfo.getAlreadyRemovedElements().contains(elem.getAppliedFunction())) {
				mFaAuxData.addAfParent(elem.getAppliedFunction(), elem);
			}
			if (!remInfo.getAlreadyRemovedElements().contains(elem.getArgument())) {
				mFaAuxData.addArgParent(elem.getArgument(), elem);
			}
		}

		final HashRelation<ELEM, ELEM> equalitiesToPropagate = getAuxData().registerNewElement(elem);

		if (remInfo == null) {
			mManager.addElement(this, elem.getAppliedFunction(), true, true);
			mManager.addElement(this, elem.getArgument(), true, true);
		} else {
			if (!remInfo.getAlreadyRemovedElements().contains(elem.getAppliedFunction())) {
				addElementRec(elem.getAppliedFunction(), remInfo);
			}
			if (!remInfo.getAlreadyRemovedElements().contains(elem.getArgument())) {
				addElementRec(elem.getArgument(), remInfo);
			}
		}


		if (remInfo == null) {
			for (final Entry<ELEM, ELEM> eq : equalitiesToPropagate.entrySet()) {
				reportEqualityRec(eq.getKey(), eq.getValue());
				if (isInconsistent()) {
					// propagated equality made this Cc inconsistent (break or return here?)
					break;
				}
			}
		} else {
			// do nothing in this case, right?..
		}

//		assert sanityCheck();
	}

	public ELEM getRepresentativeElement(final ELEM elem) {
		final ELEM result = mElementTVER.getRepresentative(elem);
		if (result == null) {
			throw new IllegalArgumentException(
					"Use this method only for elements that you know have been added already");
		}
		return result;
	}

	public Set<ELEM> collectElementsToRemove(final ELEM elem) {
		final Set<ELEM> result = new HashSet<>();

		// collect transitive parents of dependent elements
		result.addAll(mFaAuxData.getDependentsOf(elem));
		for (final ELEM dep : mFaAuxData.getDependentsOf(elem)) {
			result.addAll(collectTransitiveParents(dep));
		}

		result.addAll(collectTransitiveParents(elem));

		return result;
	}

	private Set<ELEM> collectTransitiveParents(final ELEM elem) {
		final Set<ELEM> result = new HashSet<>();

		final Deque<ELEM> worklist = new ArrayDeque<>();
		worklist.add(elem);

		while (!worklist.isEmpty()) {
			final ELEM current = worklist.pop();
			result.add(current);

			worklist.addAll(mFaAuxData.getAfParents(current));
			worklist.addAll(mFaAuxData.getArgParents(current));
		}
		return result;
	}

	/**
	 *
	 * @param elem
	 * @param elementsToRemove
	 * @param nodeToReplacementNode
	 * @param useWeqGpa
	 *
	 * @return a set of nodes that have been added to dependent objects (weakEqLabels in the WeqCC case)
	 *		 empty set for this class (only meaningful in subclasses)
	 */
	public void removeElements(final Set<ELEM> elementsToRemove, final Map<ELEM, ELEM> nodeToReplacementNode) {
		assert !mIsFrozen;

		for (final ELEM etr : elementsToRemove) {
			mFaAuxData.removeFromNodeToDependents(etr);
		}

		// remove from this cc
		for (final ELEM etr : elementsToRemove) {
			if (!hasElement(etr)) {
				continue;
			}
			updateElementTverAndAuxDataOnRemoveElement(etr, nodeToReplacementNode.get(etr));
		}
//		return Collections.emptySet();
	}

//	@Override
//	public void applyClosureOperations() {
//		// do nothing here at them moment (but in overriding methods)
//	}

	/**
	 *
	 * @param elemToRemove
	 * @param elemToRemoveIsAppliedFunctionNotArgument serves as info which elements are currently being removed -- we don't want to schedule
	 *   any of these for adding
	 * @param elemToRemoveToReplacement this method may schedule elements for adding that can replace elements being
	 *   removed -- it should update this map accordingly
	 * @return
	 */
	public Set<ELEM> getNodesToIntroduceBeforeRemoval(final ELEM elemToRemove, final Set<ELEM> elementsToRemove,
			final Map<ELEM, ELEM> elemToRemoveToReplacement) {

		assert elementsToRemove.contains(elemToRemove);
//		assert elemToRemoveToReplacement.keySet().equals(mElementCurrentlyBeingRemoved.getRemovedElements());

		/*
		 * say
		 * <li> elemToRemove = a[i]
		 * <li> elemToRemove does not have an equivalence class member to replace it with (assumed by this method)
		 * <li> isConstrained(a[i]) (assumed by this method)
		 * <li> (case1) a[i] is removed because a is removed, and exists b ~ a, then return b[i] (to be added later)
		 * <li> (case2) a[i] is removed because i is removed, and exists i ~ j, then return a[j] (to be added later)
		 */
		assert elemToRemove.isFunctionApplication();
		/*
		 *  it is tempting to make the following assertion, but not what we want:
		 *   assume we have {x, y}, then we have a replacement for x for all other purposes, but not for the purpose
		 *    of keeping the "y equals something" constraint
		 */
//		assert getOtherEquivalenceClassMember(elemToRemove, elemToRemoveToReplacement.keySet()) == null;

		/*
		 *  case split on which child of elemToRemove is a reason for elemToRemove being scheduled for removal
		 *  three cases: appliedfunction, argument, both
		 */
		final boolean etrIsRemovedBecauseOfAf =
				elementsToRemove.contains(elemToRemove.getAppliedFunction());
		final boolean etrIsRemovedBecauseOfArg =
				elementsToRemove.contains(elemToRemove.getArgument());

		if (etrIsRemovedBecauseOfAf && etrIsRemovedBecauseOfArg) {
			// look for b with a ~ b, and j with i ~ j
			final ELEM afReplacement = getOtherEquivalenceClassMember(elemToRemove.getAppliedFunction(),
				elementsToRemove);
			final ELEM argReplacement = getOtherEquivalenceClassMember(elemToRemove.getArgument(),
					elementsToRemove);
			if (afReplacement != null && argReplacement != null) {
				final ELEM afReplaced = elemToRemove.replaceAppliedFunction(afReplacement);
				final ELEM afAndArgReplaced = afReplaced.replaceArgument(argReplacement);
				assert !mElementCurrentlyBeingRemoved.getRemovedElements().contains(afAndArgReplaced);
				elemToRemoveToReplacement.put(elemToRemove, afAndArgReplaced);
				if (!hasElement(afAndArgReplaced)) {
					assert nodeToAddIsEquivalentToOriginal(afAndArgReplaced, elemToRemove);
					return Collections.singleton(afAndArgReplaced);
				} else {
					return Collections.emptySet();
				}
			}
		} else if (etrIsRemovedBecauseOfAf) {
			// look for b with a ~ b
			final ELEM afReplacement = getOtherEquivalenceClassMember(elemToRemove.getAppliedFunction(),
					elementsToRemove);
			if (afReplacement != null) {
				final ELEM afReplaced = elemToRemove.replaceAppliedFunction(afReplacement);
				assert !mElementCurrentlyBeingRemoved.getRemovedElements().contains(afReplaced);
				elemToRemoveToReplacement.put(elemToRemove, afReplaced);
				if (!hasElement(afReplaced)) {
					assert nodeToAddIsEquivalentToOriginal(afReplaced, elemToRemove);
					return Collections.singleton(afReplaced);
				} else {
					return Collections.emptySet();
				}
			}
		} else {
			// look for j with i ~ j
			final ELEM argReplacement = getOtherEquivalenceClassMember(elemToRemove.getArgument(),
					elementsToRemove);
			if (argReplacement != null) {
				final ELEM argReplaced = elemToRemove.replaceArgument(argReplacement);
				assert !mElementCurrentlyBeingRemoved.getRemovedElements().contains(argReplaced);
				elemToRemoveToReplacement.put(elemToRemove, argReplaced);
				if (!hasElement(argReplaced)) {
					assert nodeToAddIsEquivalentToOriginal(argReplaced, elemToRemove);
					return Collections.singleton(argReplaced);
				} else {
					return Collections.emptySet();
				}
			}
		}
		return Collections.emptySet();
	}

	private boolean nodeToAddIsEquivalentToOriginal(final ELEM afAndArgReplaced, final ELEM elemToRemove) {
		final CongruenceClosure<ELEM> copy = mManager.copyNoRemInfoUnfrozen(this);
		mManager.addElement(copy, afAndArgReplaced, true, false);
		if (copy.getEqualityStatus(afAndArgReplaced, elemToRemove) != EqualityStatus.EQUAL) {
			assert false;
			return false;
		}
		return true;
	}

//	/**
//	 * If elem is alone in its equivalence class, return null.
//	 * Otherwise return any element from elem's equivalence class that is not elem.
//	 *
//	 * The user may specify a preference, i.e., if some element from the given set can be picked, it is picked.
//	 *
//	 * @param elem
//	 * @param preferredReplacements
//	 * @return
//	 */
//	protected ELEM getOtherEquivalenceClassMember(final ELEM elem) {
//		return getOtherEquivalenceClassMember(elem, null);
//	}

	/**
	 *
	 * If elem is alone in its equivalence class, return null.
	 * Otherwise return any element from elem's equivalence class that is not elem.
	 *
	 *
	 * @param argument
	 * @param forbiddenSet optional, a set whose members we don't want returned, so only look for an elemen in
	 *    equivalenceClassOf(argument) \ forbiddenSet
	 * @return
	 */
	public ELEM getOtherEquivalenceClassMember(final ELEM eqmember, final Set<ELEM> forbiddenSet) {

		assert hasElement(eqmember);
		final Set<ELEM> eqc = mElementTVER.getEquivalenceClass(eqmember);
		if (eqc.size() == 1) {
			return null;
		}
		final Optional<ELEM> opt = eqc.stream().filter(e -> !e.equals(eqmember) &&
				(forbiddenSet == null || !forbiddenSet.contains(e))).findFirst();
		if (opt.isPresent()) {
			return opt.get();
		}
		return null;
	}

	private ELEM updateElementTverAndAuxDataOnRemoveElement(final ELEM elem, final ELEM newRepChoice) {
		final boolean elemWasRepresentative = mElementTVER.isRepresentative(elem);

		final ELEM newRep = mElementTVER.removeElement(elem, newRepChoice);
		assert !elemWasRepresentative || newRepChoice == null || newRep == newRepChoice;

		getAuxData().removeElement(this, elem, elemWasRepresentative, newRep);
		if (elem.isFunctionApplication()) {
			mFaAuxData.removeAfParent(elem.getAppliedFunction(), elem);
			mFaAuxData.removeArgParent(elem.getArgument(), elem);
		}
		return newRep;
	}

//	/**
//	 * before removing the parents:
//	 * if there is a newRep, insert a node where the subnode elem is replaced by newRep
//	 * (this may introduce fresh nodes!)
//	 *
//	 * @param elem the element we are about to remove
//	 * @param preferredReplacements
//	 */
//	private void addNodesEquivalentToNodesWithRemovedElement(final ELEM elem) {
//		final ELEM otherRep = getOtherEquivalenceClassMember(elem);
//		if (otherRep != null) {
//			for (final ELEM parent : new ArrayList<>(mFaAuxData.getAfParents(elem))) {
//				assert parent.getAppliedFunction() == elem;
//				final ELEM replaced = parent.replaceAppliedFunction(otherRep);
//				mManager.addElement(this, replaced, true, true);
//			}
//			for (final ELEM parent : new ArrayList<>(mFaAuxData.getArgParents(elem))) {
//				assert parent.getArgument() == elem;
//				final ELEM replaced = parent.replaceArgument(otherRep);
//				mManager.addElement(this, replaced, true, true);
//			}
//		}
//	}

	CongruenceClosure<ELEM> join(final CongruenceClosure<ELEM> other) {
		assert !this.isInconsistent() && !other.isInconsistent() && !this.isTautological() && !other.isTautological();

		final CongruenceClosure<ELEM> thisAligned = mManager.addAllElements(this, other.getAllElements(), null, false);
		final CongruenceClosure<ELEM> otherAligned = mManager.addAllElements(other, this.getAllElements(), null, false);

		final ThreeValuedEquivalenceRelation<ELEM> newElemTver = thisAligned.mElementTVER
				.join(otherAligned.mElementTVER);

		return mManager.getCongruenceClosureFromTver(newElemTver, true);
	}

	public CongruenceClosure<ELEM> meetRec(final CongruenceClosure<ELEM> other, final IRemovalInfo<ELEM> remInfo,
			final boolean inplace) {
		assert !this.isInconsistent();
		/*
		 * if we are meeting in place, we make this inconsistent by adding enough constraints from other (might be
		 * optimized..)
		 */
		assert !other.isInconsistent() || inplace;

		CongruenceClosure<ELEM> thisAligned = mManager.addAllElements(this, other.getAllElements(), remInfo,
				inplace);

		for (final Entry<ELEM, ELEM> eq : other.getSupportingElementEqualities().entrySet()) {
			if (thisAligned.isInconsistent()) {
				if (inplace) {
					return thisAligned;
				} else {
					return mManager.getInconsistentCc();
				}
			}
			thisAligned = mManager.reportEquality(eq.getKey(), eq.getValue(), thisAligned, inplace);
		}
		for (final Entry<ELEM, ELEM> deq : other.getElementDisequalities()) {
			if (thisAligned.isInconsistent()) {
				if (inplace) {
					return thisAligned;
				} else {
					return mManager.getInconsistentCc();
				}
			}
			thisAligned = mManager.reportDisequality(deq.getKey(), deq.getValue(), thisAligned, inplace);
		}

		return thisAligned;
	}

	/**
	 * Returns a new CongruenceClosure instance that is the meet of "this" and "other".
	 *
	 * @param other
	 * @return
	 */
	public CongruenceClosure<ELEM> meetRec(final CongruenceClosure<ELEM> other, final boolean inplace) {
		return meetRec(other, null, inplace);
	}

	/**
	 *
	 * @param other
	 * @return true iff this CongruenceClosure is equally or more constraining, than
	 *         the other given CongruenceClosure
	 */
	public boolean isStrongerThan(final CongruenceClosure<ELEM> other) {
		if (this.isInconsistent()) {
			return true;
		}
		if (other.isInconsistent()) {
			// we know this != False, and other = False
			return false;
		}
		if (other.isTautological()) {
			return true;
		}
		if (this.isTautological()) {
			// we know other != True, and this = True
			return false;
		}
		final CongruenceClosure<ELEM> thisAligned = mManager.getCopy(this, true);
		mManager.addAllElements(thisAligned, other.getAllElements(), null, true);
		// freeze not necessary but to make clear that thisAligned is closed at this point
		thisAligned.freeze();

		assert assertElementsAreSuperset(thisAligned, other);
		final CongruenceClosure<ELEM> otherAligned = mManager.getCopy(other, true);
		mManager.addAllElements(otherAligned, this.getAllElements(), null, true);
		// freeze not necessary but to make clear that thisAligned is closed at this point
		otherAligned.freeze();

		assert assertElementsAreSuperset(thisAligned, otherAligned);
		assert assertElementsAreSuperset(otherAligned, thisAligned);

		return checkIsStrongerThan(thisAligned, otherAligned);
	}

	/**
	 * We check for each equivalence representative in "other" if its equivalence
	 * class is a subset of the equivalence class of the representative in "this".
	 *
	 * (going through the representatives in "this" would be unsound because we
	 * might not see all relevant equivalence classes in "other")
	 *
	 * assumes that this and other have the same elements and functions
	 *
	 * Induces a non-strict (antisymmetric) partial ordering of the CongruenceClosure instances.
	 */
	private boolean checkIsStrongerThan(final CongruenceClosure<ELEM> thisAligned,
			final CongruenceClosure<ELEM> otherAligned) {
		assert !thisAligned.isInconsistent() && !otherAligned.isInconsistent();

		assert assertElementsAreSuperset(thisAligned, otherAligned);
		assert assertElementsAreSuperset(otherAligned, thisAligned);

		if (!isPartitionStronger(thisAligned.mElementTVER, otherAligned.mElementTVER)) {
			return false;
		}

		/*
		 * We check if each disequality that holds in "other" also holds in "this".
		 */
		if (!areDisequalitiesStrongerThan(thisAligned.mElementTVER, otherAligned.mElementTVER)) {
			return false;
		}
		return true;
	}

	public boolean isEquivalent(final CongruenceClosure<ELEM> other) {
		if (this.isInconsistent() && other.isInconsistent()) {
			return true;
		}
		if (this.isTautological() && other.isTautological()) {
			return true;
		}
		if (other.isInconsistent() || this.isInconsistent()) {
			return false;
		}
		if (other.isTautological() || this.isTautological()) {
			return false;
		}

		final CongruenceClosure<ELEM> thisAligned =
				mManager.addAllElements(this, other.getAllElements(), null, false);
		final CongruenceClosure<ELEM> otherAligned =
				mManager.addAllElements(other, this.getAllElements(), null, false);
		return checkIsStrongerThan(thisAligned, otherAligned) && checkIsStrongerThan(otherAligned, thisAligned);
	}

	private static <E> boolean areDisequalitiesStrongerThan(final ThreeValuedEquivalenceRelation<E> thisTVER,
			final ThreeValuedEquivalenceRelation<E> otherTVER) {
		for (final E rep : otherTVER.getAllRepresentatives()) {
			for (final E disequalRep : otherTVER.getRepresentativesUnequalTo(rep)) {
				if (thisTVER.getEqualityStatus(rep, disequalRep) != EqualityStatus.NOT_EQUAL) {
					return false;
				}
			}
		}
		return true;
	}

	/**
	 *
	 * @param first
	 * @param second
	 * @return true if first is stronger/more constraining than second
	 */
	private static <E> boolean isPartitionStronger(final ThreeValuedEquivalenceRelation<E> first,
			final ThreeValuedEquivalenceRelation<E> second) {
		final Collection<E> representativesFromBoth = new ArrayList<>(first.getAllRepresentatives().size()
				+ second.getAllRepresentatives().size());
		representativesFromBoth.addAll(first.getAllRepresentatives());
		representativesFromBoth.addAll(second.getAllRepresentatives());

		for (final E rep : representativesFromBoth) {
			final Set<E> eqInOther = second.getEquivalenceClass(rep);
			final Set<E> eqInThis = first.getEquivalenceClass(rep);
			if (!eqInThis.containsAll(eqInOther)) {
				return false;
			}
		}
		return true;
	}

	public EqualityStatus getEqualityStatus(final ELEM elem1, final ELEM elem2) {
		assert hasElement(elem1) && hasElement(elem2);

		final ELEM rep1 = getRepresentativeElement(elem1);
		final ELEM rep2 = getRepresentativeElement(elem2);

		if (rep1.equals(rep2)) {
			return EqualityStatus.EQUAL;
		} else if (rep1.isLiteral() && rep2.isLiteral()) {
			return EqualityStatus.NOT_EQUAL;
		}
		return mElementTVER.getEqualityStatus(elem1, elem2);
	}

	public Set<ELEM> getAllElements() {
		return Collections.unmodifiableSet(mElementTVER.getAllElements());
	}

	protected Set<Entry<ELEM, ELEM>> getPairsWithMatchingType(final Set<ELEM> baseSet,
			final boolean getReflexive, final boolean getSymmetric) {
		return CrossProducts.binarySelectiveCrossProduct(baseSet, getReflexive, getSymmetric)
				.entrySet().stream()
				.filter(en -> en.getKey().hasSameTypeAs(en.getValue()))
				.collect(Collectors.toSet());
	}

	public boolean isInconsistent() {
		return mElementTVER == null || mElementTVER.isInconsistent();
	}

	private boolean assertElementsAreSuperset(final Set<ELEM> a, final Set<ELEM> b) {
		final Set<ELEM> difference = DataStructureUtils.difference(b, a);
		if (!difference.isEmpty()) {
			assert false;
			return false;
		}
		return true;

	}

	/**
	 * check that elements in a are a superset of elements in b
	 * @param a
	 * @param b
	 * @return
	 */
	private boolean assertElementsAreSuperset(final CongruenceClosure<ELEM> a,
			final CongruenceClosure<ELEM> b) {
		final Set<ELEM> difference = DataStructureUtils.difference(b.getAllElements(), a.getAllElements());
		if (!difference.isEmpty()) {
			assert false;
			return false;
		}
		return true;
	}

	public boolean assertAtMostOneLiteralPerEquivalenceClass() {
		if (isInconsistent()) {
			return true;
		}
		for (final Set<ELEM> eqc : mElementTVER.getAllEquivalenceClasses()) {
			assert eqc.stream().filter(e -> e.isLiteral()).collect(Collectors.toList()).size() < 2;
		}
		return true;
	}

	public boolean assertSimpleElementIsFullyRemoved(final ELEM elem) {

		// not ideal as this method is used during the removal, too..
		final Set<ELEM> transitiveParents = collectElementsToRemove(elem);

		for (final ELEM e : getAllElements()) {
			if (transitiveParents.contains(e)) {
				assert false;
				return false;
			}
		}
		return true;
	}

	public boolean assertSingleElementIsFullyRemoved(final ELEM elem) {
//		for (final Entry<ELEM, ELEM> en : mNodeToDependents.entrySet()) {
		for (final Entry<ELEM, ELEM> en : mFaAuxData.getNodeToDependentPairs()) {
			if (en.getKey().equals(elem) || en.getValue().equals(elem)) {
				assert false;
				return false;
			}
		}

		return assertElementIsFullyRemovedOnlyCc(elem);
	}

	/**
	 * Checks  for any remainig entries of elem, does not look for subterms.
	 * @param elem
	 * @return
	 */
	protected boolean assertElementIsFullyRemovedOnlyCc(final ELEM elem) {
		if (mElementTVER.getRepresentative(elem) != null) {
			assert false;
			return false;
		}
		return true;
	}

	public boolean assertHasOnlyWeqVarConstraints(final Set<ELEM> allWeqNodes) {
			if (isTautological()) {
				return true;
			}

			final Set<ELEM> elemsAppearingInADisequality = new HashSet<>();
			for (final Entry<ELEM, ELEM> deq : mElementTVER.getDisequalities().entrySet()) {
				elemsAppearingInADisequality.add(deq.getKey());
				elemsAppearingInADisequality.add(deq.getValue());
			}

			for (final Set<ELEM> eqc : mElementTVER.getAllEquivalenceClasses()) {
				if (eqc.size() == 1 &&
						(!mFaAuxData.getAfParents(eqc.iterator().next()).isEmpty() ||
								!mFaAuxData.getArgParents(eqc.iterator().next()).isEmpty())) {
					continue;
				}

	//			final Set<ELEM> intersection1 = DataStructureUtils.intersection(eqc, allWeqNodes);
				final Set<ELEM> intersection1 = eqc.stream().filter(eqcelem -> dependsOnAny(eqcelem, allWeqNodes))
						.collect(Collectors.toSet());
				final Set<ELEM> intersection2 = DataStructureUtils.intersection(eqc, elemsAppearingInADisequality);
				if (intersection1.isEmpty() && intersection2.isEmpty()) {
					assert false;
					return false;
				}
			}
			return true;
		}

	public boolean assertHasExternalRemInfo() {
		return mExternalRemovalInfo != null;
	}

	public boolean sanityCheck() {
		return sanityCheck(null);
	}

	protected boolean sanityCheck(final IRemovalInfo<ELEM> remInfo) {
		return sanityCheckOnlyCc(remInfo);
	}

	public boolean sanityCheckOnlyCc() {
		return sanityCheckOnlyCc(null);
	}

	/**
	 * Check for some class invariants.
	 *
	 * @return
	 */
	@SuppressWarnings("unused")
	public boolean sanityCheckOnlyCc(final IRemovalInfo<ELEM> remInfo) {
		if (mConstructorInitializationPhase) {
			return true;
		}

		if (this.isInconsistent()) {
			if (mElementTVER != null) {
				// transitory CClosure instance which will later be replaced by the "bottom" variant
				if (!mElementTVER.isInconsistent()) {
					assert false : "fields are null, but Cc is not inconsistent";
					return false;
				}
			}
			return true;
		}

		if (mElementTVER.isInconsistent()) {
					assert false : "Cc is inconsistent but fields are not null";
					return false;
		}

		/*
		 * check that each element in ccpars is a function application
		 */
		for (final ELEM elem : getAllElementRepresentatives()) {
			for (final ELEM ccp : this.getAuxData().getAfCcPars(elem)) {
				if (!ccp.isFunctionApplication()) {
					assert false : "ccpar is not a funcapp";
					return false;
				}
			}
			for (final ELEM ccp : this.getAuxData().getArgCcPars(elem)) {
				if (!ccp.isFunctionApplication()) {
					assert false : "ccpar is not a funcapp";
					return false;
				}
			}
		}

		/*
		 * check that for each element that is a function application, its children are present, too
		 * However, take removalInfo into account.
		 */
		for (final ELEM elem : getAllElements()) {
			if (!elem.isFunctionApplication()) {
				continue;
			}
			if (!hasElement(elem.getAppliedFunction()) &&
					(remInfo == null || !remInfo.getRemovedElements().contains(elem.getAppliedFunction())) &&
					(mElementCurrentlyBeingRemoved == null
						|| !mElementCurrentlyBeingRemoved.getRemovedElements().contains(elem.getAppliedFunction())) &&
					(mExternalRemovalInfo == null
						|| !mExternalRemovalInfo.getRemovedElements().contains(elem.getAppliedFunction()))) {
				assert false;
				return false;
			}
			if (!hasElement(elem.getArgument()) &&
					(remInfo == null || !remInfo.getRemovedElements().contains(elem.getArgument())) &&
					(mElementCurrentlyBeingRemoved == null
						|| !mElementCurrentlyBeingRemoved.getRemovedElements().contains(elem.getArgument())) &&
					(mExternalRemovalInfo == null
						|| !mExternalRemovalInfo.getRemovedElements().contains(elem.getArgument()))) {
				assert false;
				return false;
			}
		}


		/*
		 * check that for each function application a[i], its representative's ccchild contains the corresponding
		 * af/arg-pair (a,i)
		 */
		for (final ELEM elem : getAllElements()) {
			if (!elem.isFunctionApplication()) {
				continue;
			}
			final ELEM rep = getRepresentativeElement(elem);
			if (!getAuxData().getCcChildren(rep).containsPair(elem.getAppliedFunction(), elem.getArgument())) {
				assert false : "ccchild store incomplete";
				return false;
			}
		}

		/*
		 * check that all elements with isLiteral() = true are in mAllLiterals
		 * an that every element of mAllLiterals is a literal
		 */
		for (final ELEM elem : getAllElements()) {
			if (elem.isLiteral() && !mAllLiterals.contains(elem)) {
				assert false : "all literals store incomplete";
				return false;
			}
		}
		for (final ELEM lit : mAllLiterals) {
			if (!lit.isLiteral()) {
				assert false : "non-literal in all literals store";
				return false;
			}
		}

		/*
		 * check for each equivalence class that if there is a literal in the equivalence class, it is the
		 * representative
		 */
		for (final Set<ELEM> eqc : mElementTVER.getAllEquivalenceClasses()) {
			for (final ELEM elem : eqc) {
				if (!elem.isLiteral()) {
					continue;
				}
				// elem is literal
				if (!isRepresentative(elem)) {
					// elem is a
					assert false : "literal is not the representative of its eq class";
					return false;
				}
			}
		}

		/*
		 * check that for each element, its parents in funcAppTreeAuxData and ccAuxData agree
		 */
		for (final ELEM elem : getAllElements()) {
			final Set<ELEM> afCcparFromDirectParents = new HashSet<>();
			final Set<ELEM> argCcparFromDirectParents = new HashSet<>();
			for (final ELEM eqcMember : mElementTVER.getEquivalenceClass(elem)) {
				afCcparFromDirectParents.addAll(mFaAuxData.getAfParents(eqcMember));
				argCcparFromDirectParents.addAll(mFaAuxData.getArgParents(eqcMember));
			}

			final ELEM rep = getRepresentativeElement(elem);
			if (!afCcparFromDirectParents.equals(getAuxData().getAfCcPars(rep))) {
				// d1 and d2 are not used by the program, but nice to have precomputed when the assertion fails
				final Set<ELEM> d1 =
						DataStructureUtils.difference(afCcparFromDirectParents,
								new HashSet<>(getAuxData().getAfCcPars(rep)));
				final Set<ELEM> d2 =
						DataStructureUtils.difference(new HashSet<>(getAuxData().getAfCcPars(rep)),
								afCcparFromDirectParents);
				assert false : "funcAppTreeAuxData and ccAuxData don't agree (Af case)";
				return false;
			}
			if (!argCcparFromDirectParents.equals(getAuxData().getArgCcPars(rep))) {
				// d1 and d2 are not used by the program, but nice to have precomputed when the assertion fails
				final Set<ELEM> d1 =
						DataStructureUtils.difference(argCcparFromDirectParents,
								new HashSet<>(getAuxData().getArgCcPars(rep)));
				final Set<ELEM> d2 =
						DataStructureUtils.difference(new HashSet<>(getAuxData().getArgCcPars(rep)),
								argCcparFromDirectParents);
				assert false : "funcAppTreeAuxData and ccAuxData don't agree (Arg case)";
				return false;
			}
		}

		/*
		 * check that all elements that are related are of the same type
		 * while same type means here:
		 *  - for funcApps: same number of arguments
		 *  -
		 */
		for (final ELEM e1 : getAllElements()) {
			for (final ELEM e2 : mElementTVER.getEquivalenceClass(e1)) {
				if (!e1.hasSameTypeAs(e2)) {
					assert false : "elements of incompatible type are in same eq class";
					return false;
				}
			}
		}
		for (final Entry<ELEM, ELEM> deq : mElementTVER.getDisequalities()) {
			if (!deq.getKey().hasSameTypeAs(deq.getValue())) {
				assert false : "stored disequality between elements of incompatible type";
				return false;
			}
		}

		return true;
	}

	public Map<ELEM, ELEM> getSupportingElementEqualities() {
		return mElementTVER.getSupportingEqualities();
	}

	public HashRelation<ELEM, ELEM> getElementDisequalities() {
		return mElementTVER.getDisequalities();
	}

	Map<String, Integer> summarize() {
		final Map<String, Integer> result = new HashMap<>();

		result.put("#Elements", getAllElements().size());
		result.put("#EquivalenceClasses", getAllElementRepresentatives().size());
		result.put("#SupportingEqualties", getSupportingElementEqualities().size());
		result.put("#SupportingDisequalties", getElementDisequalities().size());

		return result;
	}

	@Override
	public String toString() {
		if (isTautological()) {
			return "True";
		}
		if (isInconsistent()) {
			return "False";
		}
		if (getAllElements().size() < CcSettings.MAX_NO_ELEMENTS_FOR_VERBOSE_TO_STRING) {
			return toLogString();
		}

		final StringBuilder sb = new StringBuilder();
		for (final Entry<String, Integer> en : summarize().entrySet()) {
			sb.append(String.format("%s : %d\n", en.getKey(), en.getValue()));
		}

		return sb.toString();
	}

	public String toLogString() {
		if (isTautological()) {
			return "True";
		}
		if (isInconsistent()) {
			return "False";
		}

		final StringBuilder sb = new StringBuilder();
		sb.append("--CC(begin):--\n");

		sb.append("Equivalences:\n");
		for (final Set<ELEM> eqc : mElementTVER.getAllEquivalenceClasses()) {
			sb.append(eqc);
			if (eqc.size() > 1) {
				sb.append(" --- rep: ");
				sb.append(mElementTVER.getRepresentative(eqc.iterator().next()));
			}
			sb.append("\n");
		}
		sb.append("Disequalities:\n");
		for (final Entry<ELEM, ELEM> deq : mElementTVER.getDisequalities()) {
			sb.append(deq.getKey());
			sb.append(" != ");
			sb.append(deq.getValue());
			sb.append("\n");
		}
		sb.append("--CC(end):--\n");

		return sb.toString();
	}

	static <E> boolean haveSameElements(final ThreeValuedEquivalenceRelation<E> tver1,
			final ThreeValuedEquivalenceRelation<E> tver2) {
		return tver1.getAllElements().equals(tver2.getAllElements());
	}



//	static <E> Collection<E> concatenateCollections(final Collection<E> c1, final Collection<E> c2) {
//		final Collection<E> result = getFreshCollection(c1, c1.size() + c2.size());
//		result.addAll(c2);
//		return result;
//	}
//
//	static <E> Collection<E> getFreshCollection(final Collection<E> oldCollection, final int capacity) {
//		final Collection<E> newCollection = new ArrayList<>(capacity);
//		newCollection.addAll(oldCollection);
//		return newCollection;
//	}

	public boolean isTautological() {
		if (isInconsistent()) {
			return false;
		}
		return mElementTVER.isTautological();
	}

	/**
	 * Replaces all ELEMs and ELEMs with transformed versions in place.
	 * The transformation is done by the given Functions.
	 *
	 * @param elemTransformer
	 * @param functionTransformer
	 * @return
	 */
	public void transformElementsAndFunctions(final Function<ELEM, ELEM> elemTransformer) {
		assert !mIsFrozen;
//		assert sanitizeTransformer(elemTransformer, getAllElements()) : "we assume that the transformer does not "
//				+ "produce elements that were in the relation before!";

		mElementTVER.transformElements(elemTransformer);
		getAuxData().transformElements(elemTransformer);
		mFaAuxData.transformElements(elemTransformer);
	}


	/**
	 * We demand that if our transformer changes an element, it may not be in the original set of elements
	 * @param elemTransformer
	 * @param transformedSet
	 * @return
	 */
	private static <E> boolean sanitizeTransformer(final Function<E, E> elemTransformer, final Set<E> inputSet) {
		for (final E el :inputSet) {
			final E transformed = elemTransformer.apply(el);
			if (el.equals(transformed)) {
				// nothing to check
				continue;
			}
			if (inputSet.contains(transformed)) {
				assert false;
				return false;
			}
		}
		return true;
	}

	public boolean hasElements(final ELEM... elems) {
		for (final ELEM e : elems) {
			if (!hasElement(e)) {
				return false;
			}
		}
		return true;
	}

	public boolean hasElement(final ELEM elem) {
		return getAllElements().contains(elem);
	}

	/**
	 * We call a node constrained iff this CongruenceClosure puts any non-tautological constraint on it.
	 * In particular, the node elem is constrained if both of the following conditions hold
	 * <li> elem is the only member of its equivalence class
	 * <li> elem does not appear in a disequality
	 *
	 * @param elem
	 * @return true
	 */
	public boolean isConstrained(final ELEM elem) {
		if (!hasElement(elem)) {
			return false;
		}
		if (mElementTVER.isConstrained(elem)) {
			return true;
		}
		for (final ELEM afpar : mFaAuxData.getAfParents(elem)) {
			if (isConstrained(afpar)) {
				return true;
			}
		}
		for (final ELEM argpar : mFaAuxData.getArgParents(elem)) {
			if (isConstrained(argpar)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Returns a new CongruenceClosure which contains only those constraints in this CongruenceClosure that constrain
	 *  at least one of the given elements.
	 *
	 * <li> Say elemsToKeep contains a variable q, and we have {q, i} {a[i], j}, then we make explicit that the second
	 * conjunct constrains q, too, by adding the node a[q], we get {q, i} {a[q], a[i], j}.
	 * <li> we may call this during a remove-operation (where this Cc labels a weak equivalence edge in a weqCc, and
	 *  in the weqCc we are in the process of removing elements).
	 *  That means that we may not introduce elements that are currently being removed, in particular, it may be the
	 *  case that this Cc has a parent a[i], but not the child element i. We may not do anything that adds i back.
	 *  (sanity checks have to account for this by taking into account the removeElementInfo, that we are passing
	 *  around).
	 *
	 *
	 * @param elemsToKeep
	 * @param removeElement
	 * @return
	 */
	CongruenceClosure<ELEM> projectToElements(final Set<ELEM> elemsToKeep,
			final IRemovalInfo<ELEM> removeElementInfo) {
		assert !mIsFrozen;
		if (isInconsistent()) {
			return this;
		}

		/*
		 *  we need to augment the set such that all equivalent elements are contained, too.
		 *  example:
		 *   we project to {q}
		 *   current partition: {q, i} {a[i], 0}
		 *   then the second block implicitly puts a constraint on q, too, thus we need to keep it.
		 *   --> this principle applies transitively, i.e., say we have {a[q], x} {b[x], y}...
		 */

		final CongruenceClosure<ELEM> copy = mManager.getCopyWithRemovalInfo(this, removeElementInfo);


		final Set<ELEM> worklist = new HashSet<>(elemsToKeep);
		final Set<ELEM> constraintsToKeepReps = new HashSet<>();
		final Set<ELEM> visitedEquivalenceClassElements = new HashSet<>();


		while (!worklist.isEmpty()) {
//			assert copy.sanityCheck(removeElementInfo);
			assert copy.sanityCheck();

			final ELEM current = worklist.iterator().next();
			worklist.remove(current);


			if (!copy.hasElement(current)) {
				continue;
			}
			visitedEquivalenceClassElements.addAll(copy.mElementTVER.getEquivalenceClass(current));

			assert copy.mElementTVER.getEquivalenceClass(current).stream()
				.anyMatch(e -> dependsOnAny(e, elemsToKeep));
			constraintsToKeepReps.add(current);

			for (final ELEM afccpar : new HashSet<>(copy.getAuxData().getAfCcPars(copy.getRepresentativeElement(current)))) {
				if (visitedEquivalenceClassElements.contains(afccpar)) {
					continue;
				}
				final ELEM substituted = afccpar.replaceAppliedFunction(current);
				if (constraintsToKeepReps.contains(substituted)) {
					continue;
				}
				if (removeElementInfo != null
						&& dependsOnAny(substituted, removeElementInfo.getRemovedElements())) {
					// don't add anything that is currently being removed or depends on it
					continue;
				}
				assert removeElementInfo == null
						|| !dependsOnAny(substituted, removeElementInfo.getRemovedElements());
				assert dependsOnAny(substituted, elemsToKeep);
				mManager.addElement(copy, substituted, true, false);
				worklist.add(substituted);
			}
			for (final ELEM argccpar : new HashSet<>(copy.getAuxData().getArgCcPars(copy.getRepresentativeElement(current)))) {
				if (visitedEquivalenceClassElements.contains(argccpar)) {
					continue;
				}
				final ELEM substituted = argccpar.replaceArgument(current);
				if (constraintsToKeepReps.contains(substituted)) {
					continue;
				}
				if (removeElementInfo != null
						&& dependsOnAny(substituted, removeElementInfo.getRemovedElements())) {
					// don't add anything that is currently being removed or depends on it
					continue;
				}
				assert removeElementInfo == null
						|| !dependsOnAny(substituted, removeElementInfo.getRemovedElements());
				assert dependsOnAny(substituted, elemsToKeep);
				mManager.addElement(copy, substituted, true, false);
				worklist.add(substituted);
			}
		}
		// TVER does not know about parent/child relationship of nodes, so it is safe
		final ThreeValuedEquivalenceRelation<ELEM> newTver =
				copy.mElementTVER.filterAndKeepOnlyConstraintsThatIntersectWith(constraintsToKeepReps);
		/*
		 *  (former BUG!!!) this constructor may not add all child elements for all remaining elements, therefore
		 *  we either need a special constructor or do something else..
		 */
		return mManager.getCongruenceClosureFromTver(newTver, removeElementInfo, true);
	}

	public Collection<ELEM> getAllElementRepresentatives() {
		return mElementTVER.getAllRepresentatives();
	}

	/**
	 * Determines if one of the descendants of given element elem is a member of the given element set sub.
	 *
	 * @param elem
	 * @param sub
	 * @return
	 */
	public static <ELEM extends ICongruenceClosureElement<ELEM>> boolean dependsOnAny(final ELEM elem,
			final Set<ELEM> sub) {

		if (elem.isDependent()) {
			if (!DataStructureUtils.intersection(elem.getSupportingNodes(), sub).isEmpty()) {
				return true;
			}
		}

		if (sub.contains(elem)) {
			return true;
		}
		if (elem.isFunctionApplication()) {
			return dependsOnAny(elem.getAppliedFunction(), sub) || dependsOnAny(elem.getArgument(), sub);
		}
		return false;
	}

	@Override
	public IRemovalInfo<ELEM> getElementCurrentlyBeingRemoved() {
		return mElementCurrentlyBeingRemoved;
	}

	public void setExternalRemInfo(final IRemovalInfo<ELEM> remInfo) {
		assert mExternalRemovalInfo == null || mExternalRemovalInfo == remInfo;
		mExternalRemovalInfo = remInfo;
	}

	public boolean isRepresentative(final ELEM elem) {
		return mElementTVER.isRepresentative(elem);
	}

	public CcAuxData<ELEM> getAuxData() {
		return mAuxData;
	}

	/**
	 * auxiliary data related to the tree where an edge a -> b means that b is an argument to function a
	 * (this is mostly/only needed for element removal)
	 */
	protected class FuncAppTreeAuxData {
		// these cannot be managed within the nodes because the nodes are shared between CongruenceClosure instances!
		private final HashRelation<ELEM, ELEM> mDirectAfPars;
		private final HashRelation<ELEM, ELEM> mDirectArgPars;


		private final HashRelation<ELEM, ELEM> mNodeToDependents;

		FuncAppTreeAuxData() {
			mDirectAfPars = new HashRelation<>();
			mDirectArgPars = new HashRelation<>();
			mNodeToDependents = new HashRelation<>();
		}

		FuncAppTreeAuxData(final CongruenceClosure<ELEM>.FuncAppTreeAuxData faAuxData) {
			mDirectAfPars = new HashRelation<>(faAuxData.mDirectAfPars);
			mDirectArgPars = new HashRelation<>(faAuxData.mDirectArgPars);
			mNodeToDependents = new HashRelation<>(faAuxData.mNodeToDependents);
		}

		public void addSupportingNode(final ELEM supp, final ELEM elem) {
			mNodeToDependents.addPair(supp, elem);
		}

		public void addAfParent(final ELEM elem, final ELEM parent) {
			mDirectAfPars.addPair(elem, parent);
		}

		public void addArgParent(final ELEM elem, final ELEM parent) {
			mDirectArgPars.addPair(elem, parent);
		}

		public Set<ELEM> getAfParents(final ELEM elem) {
			return Collections.unmodifiableSet(mDirectAfPars.getImage(elem));
		}

		public Set<ELEM> getArgParents(final ELEM elem) {
			return Collections.unmodifiableSet(mDirectArgPars.getImage(elem));
		}

		public void removeAfParent(final ELEM elem, final ELEM parent) {
			mDirectAfPars.removePair(elem, parent);
		}

		public void removeArgParent(final ELEM elem, final ELEM parent) {
			mDirectArgPars.removePair(elem, parent);
		}

		public void transformElements(final Function<ELEM, ELEM> elemTransformer) {
			mDirectAfPars.transformElements(elemTransformer, elemTransformer);
			mDirectArgPars.transformElements(elemTransformer, elemTransformer);

			for (final Entry<ELEM, ELEM> en : new HashRelation<>(mNodeToDependents).entrySet()) {
				mNodeToDependents.removePair(en.getKey(), en.getValue());
				mNodeToDependents.addPair(elemTransformer.apply(en.getKey()),
						elemTransformer.apply(en.getValue()));
			}
		}

		public Set<Entry<ELEM, ELEM>> getNodeToDependentPairs() {
			return mNodeToDependents.entrySet();
		}

		public Set<ELEM> getDependentsOf(final ELEM elem) {
			return mNodeToDependents.getImage(elem);
		}

		public void removeFromNodeToDependents(final ELEM etr) {
			if (etr.isDependent()) {
				mNodeToDependents.removeRangeElement(etr);
			}
			mNodeToDependents.removeDomainElement(etr);
		}
	}

	public void reportEqualityToElementTVER(final ELEM node1, final ELEM node2) {
		mElementTVER.reportEquality(node1, node2);
	}

	public boolean isElementTverInconsistent() {
		return mElementTVER.isInconsistent();
	}

	public void reportDisequalityToElementTver(final ELEM node1, final ELEM node2) {
		mElementTVER.reportDisequality(node1, node2);

	}

	public Collection<ELEM> getArgCcPars(final ELEM elem) {
		return mAuxData.getArgCcPars(elem);
	}

//	@Override
//	public void prepareForRemove(final boolean useWeqGpa) {
//		// do nothing
//	}

	public void setElementCurrentlyBeingRemoved(final IRemovalInfo<ELEM> re) {
		assert re == null || mElementCurrentlyBeingRemoved == null;
		mElementCurrentlyBeingRemoved = re;
	}

	public boolean isDebugMode() {
		return mManager.isDebugMode();
	}

	public ILogger getLogger() {
		return mManager.getLogger();
	}
}
