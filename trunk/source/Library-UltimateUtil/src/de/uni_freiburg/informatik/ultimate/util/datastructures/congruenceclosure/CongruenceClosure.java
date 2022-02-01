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
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.function.BiPredicate;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CcManager.CcBmNames;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

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
		implements IEqualityReportingTarget<ELEM>, IElementRemovalTarget<ELEM> {

	protected final ThreeValuedEquivalenceRelation<ELEM> mElementTVER;

	private final CcAuxData<ELEM> mAuxData;

	protected final CongruenceClosure<ELEM>.FuncAppTreeAuxData mFaAuxData;

	protected final Set<ELEM> mAllLiterals;

	protected boolean mIsFrozen = false;

	boolean mConstructorInitializationPhase = false;

	/**
	 * Store which element we are currently in the process of removing (a remove can trigger deep recursive calls, and
	 *  some need to know this. Also sanity checks may be done more precisely when we know this)
	 */
	protected IRemovalInfo<ELEM> mElementCurrentlyBeingRemoved;

	private IRemovalInfo<ELEM> mExternalRemovalInfo;

	private final CcManager<ELEM> mManager;

	CCLiteralSetConstraints<ELEM> mLiteralSetConstraints;

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

		mLiteralSetConstraints = new CCLiteralSetConstraints<>(manager, this);
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

		mLiteralSetConstraints = null;
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

		mLiteralSetConstraints = new CCLiteralSetConstraints<>(mManager, this);

		mConstructorInitializationPhase = true;
		// initialize the helper mappings according to mElementTVER
		for (final ELEM elem : new HashSet<>(mElementTVER.getAllElements())) {
			registerNewElement(elem, this);
		}
		mConstructorInitializationPhase = false;

		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3 || sanityCheck();
	}

	/**
	 * (called from projectToElements)
	 *
	 * @param logger a logger, can be null (isDebug will return false, then)
	 * @param newElemPartition
	 * @param remInfo
	 */
	CongruenceClosure(final CcManager<ELEM> manager, final ThreeValuedEquivalenceRelation<ELEM> newElemPartition,
			final CCLiteralSetConstraints<ELEM> literalConstraints, final IRemovalInfo<ELEM> remInfo) {
		/* Note: the following two assertions do not need to hold because this may be called during element removal
		 *  preparations*/
//		assert assertNoElementsFromRemInfoInTver(newElemPartition, remInfo);
//		assert assertNoElementsFromRemInfoInLitSetConstraints(literalConstraints, remInfo);
		assert newElemPartition.getAllElements()
			.containsAll(literalConstraints.getAllElementsMentionedInASetConstraint());
		mElementTVER = newElemPartition;
		mAuxData = new CcAuxData<>(this);
		mFaAuxData = new FuncAppTreeAuxData();
		mAllLiterals = new HashSet<>();
		mManager = manager;

		mLiteralSetConstraints = Objects.requireNonNull(literalConstraints);
		mLiteralSetConstraints.setCongruenceClosure(this);

		mConstructorInitializationPhase = true;
		// initialize the helper mappings according to mElementTVER
		for (final ELEM elem : new HashSet<>(mElementTVER.getAllElements())) {
			registerNewElement(elem, this, remInfo);
		}
		mConstructorInitializationPhase = false;
		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3 || sanityCheck(remInfo);
	}

	/**
	 * copy constructor
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
		mLiteralSetConstraints = new CCLiteralSetConstraints<>(original.mManager, this,
				original.getLiteralSetConstraints());
		// can be violated during remove (?)
		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3 || sanityCheck(externalRemovalInfo);
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
	 * Sets the flag for isFrozen() to true. (Propagations in CongruenceClosure are done immediately so no closure
	 * needs to be executed here.)
	 */
	public void freezeAndClose() {
		assert !mIsFrozen;
		mIsFrozen = true;
	}

	public boolean isFrozen() {
		return mIsFrozen;
	}

	boolean reportEquality(final ELEM elem1, final ELEM elem2) {
		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_2 || sanityCheck();
		final boolean result = reportEqualityRec(elem1, elem2);
		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_2 || sanityCheck();
		return result;
	}

	@Override
	public boolean reportEqualityRec(final ELEM elem1, final ELEM elem2) {
//		assert !elem1.isLiteral() || !elem2.isLiteral() || elem1.equals(elem2);
//		assert !hasElement(elem1) || !getRepresentativeElement(elem1).isLiteral()
//			|| !hasElement(elem2) || !getRepresentativeElement(elem2).isLiteral()
//			|| getRepresentativeElement(elem1).equals(getRepresentativeElement(elem2));
		assert !mIsFrozen;
		if (isInconsistent()) {
			throw new IllegalStateException();
		}

		boolean freshElem = false;
		freshElem |= mManager.addElementReportChange(this, elem1, true);
		freshElem |= mManager.addElementReportChange(this, elem2, true);
		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_2 || assertAtMostOneLiteralPerEquivalenceClass();

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

		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_2 || assertAtMostOneLiteralPerEquivalenceClass();

		final Pair<HashRelation<ELEM, ELEM>, HashRelation<ELEM, ELEM>> propInfo = doMergeAndComputePropagations(elem1,
				elem2);
		if (propInfo == null) {
			// this became inconsistent through the merge
			return true;
		}

		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_2 || assertAtMostOneLiteralPerEquivalenceClass();

		doFwccAndBwccPropagationsFromMerge(propInfo, this);

//		assert sanityCheck();
		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_2 || assertAtMostOneLiteralPerEquivalenceClass();
		return true;
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> void doFwccAndBwccPropagationsFromMerge(
			final Pair<HashRelation<ELEM, ELEM>, HashRelation<ELEM, ELEM>> propInfo, final IEqualityReportingTarget<ELEM> icc) {
		final HashRelation<ELEM, ELEM> equalitiesToPropagate = propInfo.getFirst();
		final HashRelation<ELEM, ELEM> disequalitiesToPropagate = propInfo.getSecond();
		/*
		 * (fwcc)
		 */
		for (final Entry<ELEM, ELEM> congruentParents : equalitiesToPropagate) {
			if (icc.isInconsistent(false)) {
				return;
			}
			icc.reportEqualityRec(congruentParents.getKey(), congruentParents.getValue());
		}

		/*
		 * (bwcc1), (bwcc2)  (-- they're only separate cases during reportDisequality)
		 */
		for (final Entry<ELEM, ELEM> unequalNeighborIndices : disequalitiesToPropagate) {
			if (icc.isInconsistent(false)) {
				return;
			}
			icc.reportDisequalityRec(unequalNeighborIndices.getKey(), unequalNeighborIndices.getValue());
		}
	}

	/**
	 * Merge the equivalence classes of the given elements and report all equality and disequality propagations that
	 * directly follow from that merge (according to fwcc and bwcc rules).
	 *
	 * @param elem1
	 * @param elem2
	 * @return
	 */
	public Pair<HashRelation<ELEM, ELEM>, HashRelation<ELEM, ELEM>> doMergeAndComputePropagations(final ELEM elem1,
			final ELEM elem2) {

		final ELEM e1OldRep = mElementTVER.getRepresentative(elem1);
		final ELEM e2OldRep = mElementTVER.getRepresentative(elem2);

		{
			constantAndMixFunctionTreatmentOnAddEquality(e1OldRep, e2OldRep, mElementTVER.getEquivalenceClass(elem1),
					mElementTVER.getEquivalenceClass(elem2), getAuxData(),
					e -> mManager.addElement(this, e, true, true), this);
		}


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

		/*
		 * It can happen we had a disequality between an element and a literal that becomes a disequality between two
		 * literals through the merge.
		 * Example:
		 *  before: {{x} {1} {3}}, x != 3
		 *    merge x, 1, new representative 1
		 *   -->  {{x, 1}, {3}}, 1 != 3
		 * We have to filter this out because we leave disequalities between literals implicit.
		 */
		if (e1OldRep.isLiteral() || e2OldRep.isLiteral()) {
			final ELEM newRep = getRepresentativeElement(elem1);
			assert newRep.isLiteral() : "if one element of an equivalence class is a literal, then it must be the "
					+ "representative";
			for (final ELEM unequalToMerged : mElementTVER.getRepresentativesUnequalTo(newRep)) {
				if (unequalToMerged.isLiteral()) {
					mElementTVER.removeDisequality(newRep, unequalToMerged);
				}
			}
		}
		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_2 || assertNoExplicitLiteralDisequalities();

		final Pair<HashRelation<ELEM, ELEM>, HashRelation<ELEM, ELEM>> propInfo =
				new Pair<>(new HashRelation<>(), new HashRelation<>());
		// literal constraint treatment
		{
			final HashRelation<ELEM, ELEM> eqToProp =
					mLiteralSetConstraints.reportEquality(e1OldRep, e2OldRep, mElementTVER.getRepresentative(elem1));
			if (eqToProp != null) {
				propInfo.getFirst().addAll(eqToProp);
			}

			if (mLiteralSetConstraints.isInconsistent()) {
				return null;
			}
		}


		final Pair<HashRelation<ELEM, ELEM>, HashRelation<ELEM, ELEM>> mergePropInfo =
				getAuxData().updateAndGetPropagationsOnMerge(elem1, elem2, e1OldRep, e2OldRep,
						oldUnequalRepsForElem1, oldUnequalRepsForElem2);
		propInfo.getFirst().addAll(mergePropInfo.getFirst());
		propInfo.getSecond().addAll(mergePropInfo.getSecond());
		return propInfo;
	}

	public Set<ELEM> getRepresentativesUnequalTo(final ELEM rep) {
		assert isRepresentative(rep);
		final Set<ELEM> result = new HashSet<>(mElementTVER.getRepresentativesUnequalTo(rep));

		/*
		 * literals are distinct from all other literals
		 */
		if (rep.isLiteral()) {
			for (final ELEM lit : mAllLiterals) {
				// don't track disequalities between different sorts -- they are always implicit
				if (lit.hasSameTypeAs(rep) && !lit.equals(rep)) {
					result.add(lit);
				}
			}
		}

		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3 || result.stream().allMatch(el -> el.hasSameTypeAs(rep))
			: "don't track disequalities between different sorts -- they are always implicit";
		return result;
	}

	boolean reportDisequality(final ELEM elem1, final ELEM elem2) {
		final boolean result = reportDisequalityRec(elem1, elem2);
		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_2 || sanityCheck();
		return result;
	}

	@Override
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

		if (elem1.isLiteral() && elem2.isLiteral()) {

			assert getEqualityStatus(elem1, elem2) == EqualityStatus.NOT_EQUAL;
			// special case: don't add a literal disequality explicitly
		} else {
			// normal case
			mElementTVER.reportDisequality(elem1, elem2);

			if (mElementTVER.isInconsistent()) {
				return true;
			}
		}

		mLiteralSetConstraints.reportDisequality(elem1, elem2);
		if (mLiteralSetConstraints.isInconsistent()) {
			return true;
		}

		final HashRelation<ELEM, ELEM> propDeqs = getAuxData().getPropagationsOnReportDisequality(elem1, elem2);

		for (final Entry<ELEM, ELEM> deq : propDeqs) {
			reportDisequalityRec(deq.getKey(), deq.getValue());
		}

		return true;
	}

	@Override
	public boolean addElement(final ELEM elem, final boolean omitSanityCheck) {
		return addElement(elem, this, omitSanityCheck);
	}

	/**
	 *
	 * Note: addElement makes calls to other non-trivial CongruenceClosure-manipulating methods addElement (recursively)
	 *  and reportEquality. We sometimes want to call these methods on an ICongruenceClosure-object that is different
	 *   from "this". (current only example: WeqCongruenceClosure.addElement which makes an addElement-call on the
	 *   CongruenceClosure inside the WeqCc.)
	 *   We call this other ICc the newEqualityTarget
	 *
	 * @param elem
	 * @param newEqualityTarget
	 * @param omitSanityCheck
	 * @return
	 */
	public boolean addElement(final ELEM elem, final IEqualityReportingTarget<ELEM> newEqualityTarget,
			final boolean omitSanityCheck) {
		final boolean result = addElementRec(elem, newEqualityTarget, null);
		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_2 || omitSanityCheck || sanityCheck();
		return result;
	}

	private boolean addElementRec(final ELEM elem, final IEqualityReportingTarget<ELEM> newEqualityTarget,
			final IRemovalInfo<ELEM> remInfo) {
		assert !mIsFrozen;
		final boolean newlyAdded = mElementTVER.addElement(elem);
		if (newlyAdded) {
			registerNewElement(elem, newEqualityTarget, remInfo);
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
	private void registerNewElement(final ELEM elem, final IEqualityReportingTarget<ELEM> newEqualityTarget) {
		registerNewElement(elem, newEqualityTarget, null);
	}

	private void registerNewElement(final ELEM elem, final IEqualityReportingTarget<ELEM> newEqualityTarget,
			final IRemovalInfo<ELEM> remInfo) {
		if (elem.isLiteral()) {
			mAllLiterals.add(elem);
		}

		if (elem.isDependentNonFunctionApplication()) {
			for (final ELEM supp : elem.getSupportingNodes()) {
				mManager.addElement(this, supp, newEqualityTarget, true, true);
				mFaAuxData.addSupportingNode(supp, elem);
			}
		}

		if (!elem.isFunctionApplication()) {
			// nothing to do
			assert mElementTVER.getRepresentative(elem) != null : "this method assumes that elem has been added "
					+ "already";
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

		// add children elements
		if (remInfo == null) {
			mManager.addElement(this, elem.getAppliedFunction(), newEqualityTarget, true, true);
			mManager.addElement(this, elem.getArgument(), newEqualityTarget, true, true);
		} else {
			if (!remInfo.getAlreadyRemovedElements().contains(elem.getAppliedFunction())) {
				mManager.addElement(this, elem.getAppliedFunction(), newEqualityTarget, true, true);
			}
			if (!remInfo.getAlreadyRemovedElements().contains(elem.getArgument())) {
				mManager.addElement(this, elem.getArgument(), newEqualityTarget, true, true);
			}
		}

		{
			constantFunctionTreatmentOnAddElement(elem,
//					(e1, e2) -> newEqualityTarget.reportEqualityRec(e1, e2),
//					e -> mManager.addElement(this, e, newEqualityTarget, true, true),
					mElementTVER.getEquivalenceClass(elem.getAppliedFunction()), newEqualityTarget);
			mixFunctionTreatmentOnAddElement(elem,
					(e, set) -> newEqualityTarget.reportContainsConstraint(e, set),
					e -> mManager.addElement(this, e, newEqualityTarget, true, true),
					mElementTVER.getEquivalenceClass(elem.getAppliedFunction()));
		}

		if (remInfo == null) {
			for (final Entry<ELEM, ELEM> eq : equalitiesToPropagate.getSetOfPairs()) {
				newEqualityTarget.reportEqualityRec(eq.getKey(), eq.getValue());
				// this seems nicer but does not work with the current CcManager
//				mManager.reportEquality(eq.getKey(),  eq.getValue(), newEqualityTarget, true);
				if (isInconsistent()) {
					// propagated equality made this Cc inconsistent (break or return here?)
					break;
				}
			}
		} else {
			// do nothing in this case, right?..
		}
	}

	/**
	 *
	 * @param elem elem that is a function application
	 * @param reportEquality
	 * @param addElement
	 * @param weakOrStrongEquivalenceClassOfAppliedFunction set of elements that are equal or weakly equal to the applied function
	 *   of elem
	 */
	public static <ELEM extends ICongruenceClosureElement<ELEM>> void constantFunctionTreatmentOnAddElement(
			final ELEM elem,
//			final BiConsumer<ELEM, ELEM> reportEquality, final Consumer<ELEM> addElement,
			final Set<ELEM> weakOrStrongEquivalenceClassOfAppliedFunction,
			final IEqualityReportingTarget<ELEM> newEqualityTarget) {
		/*
		 * treatment for constant functions:
		 *  <li> if we are adding an element of the form f(x), where f is a constant function, and v is f's
		 *   constant value then we add the equality "f(x) = v"
		 *  <li> if we are adding an element the form f(x), where f ~ g and g is a constant function,
		 *   then we add the element g(x)
		 */
		if (elem.getAppliedFunction().isConstantFunction() && !newEqualityTarget.isInconsistent(false)) {
//			reportEquality.accept(elem, elem.getAppliedFunction().getConstantFunctionValue());
			newEqualityTarget.reportEqualityRec(elem, elem.getAppliedFunction().getConstantFunctionValue());
		}
		for (final ELEM equivalentFunction : weakOrStrongEquivalenceClassOfAppliedFunction) {
			if (newEqualityTarget.isInconsistent(false)) {
				return;
			}
			if (equivalentFunction == elem.getAppliedFunction()) {
				continue;
			}
			if (equivalentFunction.isConstantFunction()) {
				// add element g(x)
//				addElement.accept(elem.replaceAppliedFunction(equivalentFunction));
				newEqualityTarget.addElement(elem.replaceAppliedFunction(equivalentFunction), false);
			}
		}
	}

	/**
	 *
	 * @param elem elem that is a function application
	 * @param reportContainsConstraint
	 * @param addElement
	 * @param weakOrStrongEquivalenceClassOfAppliedFunction set of elements that are equal or weakly equal to the applied function
	 *   of elem
	 */
	public static <ELEM extends ICongruenceClosureElement<ELEM>> void mixFunctionTreatmentOnAddElement(
			final ELEM elem, final BiConsumer<ELEM, Set<ELEM>> reportContainsConstraint,
			final Consumer<ELEM> addElement, final Set<ELEM> weakOrStrongEquivalenceClassOfAppliedFunction) {
		if (!CcSettings.SUPPORT_MIX_FUNCTION) {
			return;
		}

		/*
		 * treatment for constant functions:
		 *  <li> if we are adding an element of the form m(x), where m is a mix function, and a and b are m's
		 *   mix functions then we add the literal set constraint "m(x) in {a(x), b(x)}"
		 *  <li> if we are adding an element the form f(x), where f ~ g and g is a constant function,
		 *   then we add the element g(x)
		 */
		if (elem.getAppliedFunction().isMixFunction()) {
			final ELEM mixArray1 = elem.getAppliedFunction().getMixFunction1();
			final ELEM mixArray2 = elem.getAppliedFunction().getMixFunction2();

			final HashSet<ELEM> set = new HashSet<>();
			set.add(elem.replaceAppliedFunction(mixArray1));
			set.add(elem.replaceAppliedFunction(mixArray2));

			reportContainsConstraint.accept(elem, set);
		}
		for (final ELEM equivalentFunction : weakOrStrongEquivalenceClassOfAppliedFunction) {
			if (equivalentFunction == elem.getAppliedFunction()) {
				continue;
			}
			if (equivalentFunction.isMixFunction()) {
				// add element g(x)
				addElement.accept(elem.replaceAppliedFunction(equivalentFunction));
			}
		}
	}

	/**
	 * Constant or mix arrays can trigger addNode calls when an (possibly weak) equality is added.
	 * This method checks for nodes that trigger instantiation of the axiom for constant arrays and mix arrays.
	 * <p>
	 * This method is triggered on the addition of both weak and strong equalities.
	 * <p>
	 * background:
	 * <li> We maintain the following invariant: let f and g be (strongly or weakly) equal and let g be a constant or
	 *  mix function. Then, for every function application f(x) that is in our set of tracked elements, we also track
	 *  g(x).
	 * <li> For this method, this means, we have to go through all constant or mix function equivalent to elem1 and for
	 *   each
	 *   go through the ccpar's of f to add the corresponding nodes and vice versa.
	 *
	 * @param elemRep1 (must be a representative because we will query its afCcPars from auxdata)
	 * @param elemRep2  "
	 * @param elem1EquivalenceClass set of elements that are equal or weakly equal to elemRep1
	 * @param elem2EquivalenceClass set of elements that are equal or weakly equal to elemRep2
	 * @param congruenceClosure the congruence closure that is modified by this method (which elements are added to)
	 */
	public static <ELEM extends ICongruenceClosureElement<ELEM>> void constantAndMixFunctionTreatmentOnAddEquality(
			final ELEM elemRep1, final ELEM elemRep2, final Set<ELEM> elem1EquivalenceClass,
			final Set<ELEM> elem2EquivalenceClass, final CcAuxData<ELEM> auxData, final Consumer<ELEM> addElement,
			final IEqualityReportingTarget<ELEM> congruenceClosure) {
		for (final ELEM equivalentFunction1 : new HashSet<>(elem1EquivalenceClass)) {
			if ((CcSettings.SUPPORT_MIX_FUNCTION && equivalentFunction1.isMixFunction()) ||
					(CcSettings.SUPPORT_CONSTANT_FUNCTIONS && equivalentFunction1.isConstantFunction())) {
				// ccpar is f(x), equivalentFunction1 is g
				for (final ELEM ccpar : auxData.getAfCcPars(elemRep2)) {
					if (congruenceClosure.isInconsistent(false)) {
						return;
					}
					assert !equivalentFunction1.equals(ccpar.getAppliedFunction());
					addElement.accept(ccpar.replaceAppliedFunction(equivalentFunction1));
				}
			}
		}
		for (final ELEM equivalentFunction2 : new HashSet<>(elem2EquivalenceClass)) {
			if ((CcSettings.SUPPORT_MIX_FUNCTION && equivalentFunction2.isMixFunction()) ||
					(CcSettings.SUPPORT_CONSTANT_FUNCTIONS && equivalentFunction2.isConstantFunction())) {
				// ccpar is f(x), equivalentFunction2 is g
				for (final ELEM ccpar : auxData.getAfCcPars(elemRep1)) {
					if (congruenceClosure.isInconsistent(false)) {
						return;
					}
					assert !equivalentFunction2.equals(ccpar.getAppliedFunction());
					addElement.accept(ccpar.replaceAppliedFunction(equivalentFunction2));
				}
			}
		}
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
	 * @param elementsToRemove
	 * @param nodeToReplacementNode
	 *
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

		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_2 || sanityCheck();
	}

	/**
	 *
	 * @param elemToRemove
	 * @param elemToRemoveIsAppliedFunctionNotArgument serves as info which elements are currently being removed
	 * 		-- we don't want to schedule any of these for adding
	 * @param elemToRemoveToReplacement this method may schedule elements for adding that can replace elements being
	 *   removed -- it should update this map accordingly
	 * @return
	 */
	@Override
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
		for (final ELEM e : eqc) {
			if (!e.equals(eqmember) && (forbiddenSet == null || !forbiddenSet.contains(e))) {
				return e;
			}
		}
		return null;
	}

	private ELEM updateElementTverAndAuxDataOnRemoveElement(final ELEM elem, final ELEM newRepChoice) {
		final boolean elemWasRepresentative = mElementTVER.isRepresentative(elem);

		final ELEM newRep = mElementTVER.removeElement(elem, newRepChoice);
		assert mElementTVER.getRepresentative(newRep) == newRep;
		assert !elemWasRepresentative || newRepChoice == null || newRep == newRepChoice;

		getAuxData().removeElement(elem, elemWasRepresentative, newRep);
		if (elem.isFunctionApplication()) {
			mFaAuxData.removeAfParent(elem.getAppliedFunction(), elem);
			mFaAuxData.removeArgParent(elem.getArgument(), elem);
		}

		if (elemWasRepresentative) {
			if (newRep == null) {
				mLiteralSetConstraints.projectAway(elem);
			} else {
				mLiteralSetConstraints.replaceRepresentative(elem, newRep);
			}
		}

		return newRep;
	}

	CongruenceClosure<ELEM> join(final CongruenceClosure<ELEM> other) {
		assert !this.isInconsistent() && !other.isInconsistent() && !this.isTautological() && !other.isTautological();

		final Pair<CongruenceClosure<ELEM>, CongruenceClosure<ELEM>> aligned = mManager.alignElements(this, other,
				CcSettings.ALIGN_INPLACE && !this.isFrozen() && !other.isFrozen());
		final CongruenceClosure<ELEM> thisAligned = aligned.getFirst();
		final CongruenceClosure<ELEM> otherAligned = aligned.getSecond();

		final Triple<UnionFind<ELEM>, HashRelation<ELEM, ELEM>, HashRelation<ELEM, ELEM>> joinRes =
				thisAligned.mElementTVER.joinPartitions(otherAligned.mElementTVER);
		final UnionFind<ELEM> newPartition = joinRes.getFirst();
		final HashRelation<ELEM, ELEM> thisSplitInfo = joinRes.getSecond();
		final HashRelation<ELEM, ELEM> otherSplitInfo = joinRes.getThird();

		final HashRelation<ELEM, ELEM> newDisequalities = intersectOrUnionDisequalities(thisAligned, otherAligned,
				newPartition, true);
		final ThreeValuedEquivalenceRelation<ELEM> newElemTver = new ThreeValuedEquivalenceRelation<>(newPartition,
				newDisequalities);

		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3
			|| CcManager.isPartitionStronger(thisAligned.mElementTVER, newElemTver);
		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3
		  	|| CcManager.isPartitionStronger(otherAligned.mElementTVER, newElemTver);



		final CongruenceClosure<ELEM> newCc = mManager.getCongruenceClosureFromTver(newElemTver, true);
		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3
			|| CcManager.isPartitionStronger(thisAligned.mElementTVER, newCc.mElementTVER);
		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3
		  	|| CcManager.isPartitionStronger(otherAligned.mElementTVER, newCc.mElementTVER);

		final CCLiteralSetConstraints<ELEM> newLiteralSetConstraints =
				this.mLiteralSetConstraints.join(newCc, thisSplitInfo, otherSplitInfo, other.mLiteralSetConstraints);
		newCc.resetCcLiteralSetConstraints(newLiteralSetConstraints);

		return newCc;
	}


	private void resetCcLiteralSetConstraints(final CCLiteralSetConstraints<ELEM> newLiteralSetConstraints) {
		assert newLiteralSetConstraints.getCongruenceClosure() == this;
		mLiteralSetConstraints = newLiteralSetConstraints;
	}

	/**
	 * Conjoin or disjoin two disequality relations.
	 *
	 * @param tver1
	 * @param tver2
	 * @param newElemPartition
	 * @param intersect
	 *            conjoin or disjoin?
	 * @return
	 */
	private static <E extends ICongruenceClosureElement<E>> HashRelation<E, E> intersectOrUnionDisequalities(
			final CongruenceClosure<E> tver1, final CongruenceClosure<E> tver2, final UnionFind<E> newElemPartition,
			final boolean intersect) {
		final HashRelation<E, E> result = new HashRelation<>();

		final BiPredicate<E, E> filterForCrossProduct = (e1, e2)
				-> (e1 != e2
					&& (!e1.isLiteral() || !e2.isLiteral())
					&& e1.hasSameTypeAs(e2));

		for (final Entry<E, E> pair : CrossProducts
				.binarySelectiveCrossProduct(newElemPartition.getAllRepresentatives(), false, filterForCrossProduct)) {
			assert !(pair.getKey().isLiteral() && pair.getValue().isLiteral()) : "disequalities between literals are "
					+ "implicit, the selective cross product should have filtered these cases";

			final boolean addDisequality;
			if (intersect) {
				addDisequality = tver1.getEqualityStatus(pair.getKey(), pair.getValue()) == EqualityStatus.NOT_EQUAL
						&& tver2.getEqualityStatus(pair.getKey(), pair.getValue()) == EqualityStatus.NOT_EQUAL;
			} else {
				addDisequality = tver1.getEqualityStatus(pair.getKey(), pair.getValue()) == EqualityStatus.NOT_EQUAL
						|| tver2.getEqualityStatus(pair.getKey(), pair.getValue()) == EqualityStatus.NOT_EQUAL;
			}
			if (addDisequality) {
				result.addPair(pair.getKey(), pair.getValue());
			}
		}
		return result;
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

		for (final Entry<ELEM, SetConstraintConjunction<ELEM>> literalConstraint :
				other.getLiteralSetConstraints().getConstraints().entrySet()) {
			if (thisAligned.isInconsistent()) {
				if (inplace) {
					return thisAligned;
				} else {
					return mManager.getInconsistentCc();
				}
			}
			thisAligned = mManager.reportContainsConstraint(literalConstraint.getKey(),
					literalConstraint.getValue().getSetConstraints(),
					thisAligned, inplace);
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

	public boolean isStrongerThanNoCaching(final CongruenceClosure<ELEM> other) {
		if (isInconsistent()) {
			// mManager may be null in this case, so catch it here..
			return true;
		}
		return mManager.isStrongerThanNoCaching(this, other);
	}

	public EqualityStatus getEqualityStatus(final ELEM elem1, final ELEM elem2) {
		assert hasElement(elem1) && hasElement(elem2);
		assert !isInconsistent() : "catch this outside!";

		mManager.bmStart(CcBmNames.GET_EQUALITY_STATUS);

		if (!elem1.hasSameTypeAs(elem2)) {
			mManager.bmEnd(CcBmNames.GET_EQUALITY_STATUS);
			return EqualityStatus.NOT_EQUAL;
		}

		final ELEM rep1 = getRepresentativeElement(elem1);
		final ELEM rep2 = getRepresentativeElement(elem2);

		if (rep1.equals(rep2)) {
			mManager.bmEnd(CcBmNames.GET_EQUALITY_STATUS);
			return EqualityStatus.EQUAL;
		}

		if (rep1.isLiteral() && rep2.isLiteral()) {
			mManager.bmEnd(CcBmNames.GET_EQUALITY_STATUS);
			return EqualityStatus.NOT_EQUAL;
		}

		final Set<SetConstraint<ELEM>> litConstraint1 = mLiteralSetConstraints.getConstraint(rep1);
		final Set<SetConstraint<ELEM>> litConstraint2 = mLiteralSetConstraints.getConstraint(rep2);


//		/* if elem1 equals a literal l and litConstraint2 constrains to a literal set disjoint from l: not equal
//		 * (and vice versa) */
//		{
//			if (litConstraint2 != null) {
//				final Set<ELEM> litSet2 = mManager.getSetConstraintManager().getLiteralSet(litConstraint2);
//				if (rep1.isLiteral() && litSet2 != null && !litSet2.contains(rep1)) {
//					return EqualityStatus.NOT_EQUAL;
//				}
//			}
//			if (litConstraint1 != null) {
//				final Set<ELEM> litSet1 = mManager.getSetConstraintManager().getLiteralSet(litConstraint1);
//				if (rep2.isLiteral() && litSet1 != null && !litSet1.contains(rep2)) {
//					return EqualityStatus.NOT_EQUAL;
//				}
//			}
//		}

		if (mManager.getSetConstraintManager().meetIsInconsistent(getLiteralSetConstraints(),
						litConstraint1,
						litConstraint2)) {
			mManager.bmEnd(CcBmNames.GET_EQUALITY_STATUS);
			return EqualityStatus.NOT_EQUAL;
		}

		final EqualityStatus result = mElementTVER.getEqualityStatus(elem1, elem2);
		mManager.bmEnd(CcBmNames.GET_EQUALITY_STATUS);
		return result;
	}

	public Set<ELEM> getAllElements() {
		return Collections.unmodifiableSet(mElementTVER.getAllElements());
	}

	public CCLiteralSetConstraints<ELEM> getLiteralSetConstraints() {
		return mLiteralSetConstraints;
	}

	@Override
	public boolean isInconsistent() {
		return mElementTVER == null || mElementTVER.isInconsistent() || mLiteralSetConstraints.isInconsistent();
	}

	@Override
	public boolean isInconsistent(final boolean close) {
		// CongruenceClosure is always closed immediately..
		return isInconsistent();
	}

	private boolean assertNoElementsFromRemInfoInLitSetConstraints(
			final CCLiteralSetConstraints<ELEM> literalConstraints,
			final IRemovalInfo<ELEM> remInfo) {
		if (remInfo == null) {
			return true;
		}

		for (final Entry<ELEM, SetConstraintConjunction<ELEM>> en : literalConstraints.getConstraints().entrySet()) {
			if (dependsOnAny(en.getKey(), remInfo.getRemovedElements())) {
				return false;
			}
			if (dependsOnAny(en.getValue().getConstrainedElement(), remInfo.getRemovedElements())) {
				return false;
			}
			for (final ELEM el : en.getValue().getAllRhsElements()) {
				if (dependsOnAny(el, remInfo.getRemovedElements())) {
					return false;
				}
			}
		}
		return true;

	}

	private boolean assertNoElementsFromRemInfoInTver(final ThreeValuedEquivalenceRelation<ELEM> newElemPartition,
			final IRemovalInfo<ELEM> remInfo) {
		if (remInfo == null) {
			return true;
		}
		for (final ELEM elem : newElemPartition.getAllElements()) {
			if (dependsOnAny(elem, remInfo.getRemovedElements())) {
				return false;
			}
		}
		return true;
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
	boolean assertElementsAreSuperset(final CongruenceClosure<ELEM> a,
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
			if (allWeqNodes.isEmpty()) {
				return true;
			}

			final Set<ELEM> elemsAppearingInADisequality = new HashSet<>();
			for (final Entry<ELEM, ELEM> deq : mElementTVER.getDisequalities().getSetOfPairs()) {
				elemsAppearingInADisequality.add(deq.getKey());
				elemsAppearingInADisequality.add(deq.getValue());
			}

			for (final Set<ELEM> eqc : mElementTVER.getAllEquivalenceClasses()) {
				if (eqc.size() == 1) {// &&
//						(!mFaAuxData.getAfParents(eqc.iterator().next()).isEmpty() ||
//								!mFaAuxData.getArgParents(eqc.iterator().next()).isEmpty())) {
					continue;
				}

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

	@Override
	public boolean sanityCheck() {
		return sanityCheck(null);
	}

	public boolean sanityCheck(final IRemovalInfo<ELEM> remInfo) {
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
				if (!mElementTVER.isInconsistent() && !mLiteralSetConstraints.isInconsistent()) {
					assert false : "cc reports as inconsistent, but why?..";
					return false;
				}
			}
			return true;
		}

		if (!mElementTVER.sanityCheck()) {
					assert false;
					return false;
		}

		if (mElementTVER.isInconsistent()) {
					assert false : "Cc is inconsistent but fields are not null";
					return false;
		}

		/*
		 * check that each element in ccpars is a function application
		 */
		for (final ELEM elem : getAllRepresentatives()) {
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

		if (!assertNoExplicitLiteralDisequalities()) {
			assert false;
			return false;
		}

		if (!mLiteralSetConstraints.sanityCheck()) {
			assert false;
			return false;
		}

		return true;
	}

	private boolean assertNoExplicitLiteralDisequalities() {
		/*
		 * disequalities between literals must remain implicit
		 */
		for (final Entry<ELEM, ELEM> deq : mElementTVER.getDisequalities()) {
			if (deq.getKey().isLiteral() && deq.getValue().isLiteral()) {
				assert false : "explicit disequality between literals";
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
		result.put("#EquivalenceClasses", getAllRepresentatives().size());
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

	@Override
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
		sb.append(mLiteralSetConstraints.toString());

		sb.append("--CC(end):--\n");

		return sb.toString();
	}

	static <E> boolean haveSameElements(final ThreeValuedEquivalenceRelation<E> tver1,
			final ThreeValuedEquivalenceRelation<E> tver2) {
		return tver1.getAllElements().equals(tver2.getAllElements());
	}

	public boolean isTautological() {
		if (isInconsistent()) {
			return false;
		}
		return mElementTVER.isTautological() && mLiteralSetConstraints.isEmpty();
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
		mLiteralSetConstraints.transformElements(elemTransformer);
		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_1 || sanityCheck();
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

	@Override
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
	@Override
	public boolean isConstrained(final ELEM elem) {
		if (!hasElement(elem)) {
			return false;
		}
		if (isConstrainedDirectly(elem)) {
			return true;
		}
		if (elem.isDependentNonFunctionApplication()) {
			for (final ELEM supp : elem.getSupportingNodes()) {
				if (isConstrained(supp)) {
					return true;
				}
			}
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


	@Override
	public boolean isConstrainedDirectly(final ELEM elem) {
		if (!hasElement(elem)) {
			return false;
		}
		if (mElementTVER.isConstrained(elem)) {
			return true;
		}
		if (mLiteralSetConstraints.isConstrained(elem)) {
			return true;
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
		/* the elements constraints over which we need to keep in our result (they do not need to be representatives
		 * in the UnionFind instance but to add one element per equivalence class here suffices) */
		final Set<ELEM> elemsInConstraintsToKeep = new HashSet<>();
		final Set<ELEM> visitedEquivalenceClassElements = new HashSet<>();


		while (!worklist.isEmpty()) {
//			assert copy.sanityCheck(removeElementInfo);
			if (!CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_1) {
				assert copy.sanityCheck();
			}

			final ELEM current = worklist.iterator().next();
			worklist.remove(current);


			if (!copy.hasElement(current)) {
				continue;
			}
			visitedEquivalenceClassElements.addAll(copy.mElementTVER.getEquivalenceClass(current));

//			assert copy.mElementTVER.getEquivalenceClass(current).stream()
//				.anyMatch(e -> dependsOnAny(e, elemsToKeep));
			elemsInConstraintsToKeep.add(current);

			/*
			 * for each ccpar f(x) (afccpar as well as argccpar) of the current element q (which is related to an
			 *  element in elemsToKeep through constraints), add an element f(q) (or q(x) respectively) to the worklist,
			 *  so its equivalence class will be kept.
			 */
			for (final ELEM afccpar : new HashSet<>(copy.getAuxData().getAfCcPars(copy.getRepresentativeElement(current)))) {
				if (visitedEquivalenceClassElements.contains(afccpar)) {
					continue;
				}
				final ELEM substituted = afccpar.replaceAppliedFunction(current);
				if (elemsInConstraintsToKeep.contains(substituted)) {
					continue;
				}
				if (removeElementInfo != null
						&& dependsOnAny(substituted, removeElementInfo.getRemovedElements())) {
					// don't add anything that is currently being removed or depends on it
					continue;
				}
				assert removeElementInfo == null
						|| !dependsOnAny(substituted, removeElementInfo.getRemovedElements());
				/*
				 * dropped this assertion since because of set constraints we also need elements that do not depend on
				 * a weq var
				 */
//				assert dependsOnAny(substituted, elemsToKeep);
				mManager.addElement(copy, substituted, true, false);
				worklist.add(substituted);
			}
			for (final ELEM argccpar : new HashSet<>(copy.getAuxData().getArgCcPars(copy.getRepresentativeElement(current)))) {
				if (visitedEquivalenceClassElements.contains(argccpar)) {
					continue;
				}
				final ELEM substituted = argccpar.replaceArgument(current);
				if (elemsInConstraintsToKeep.contains(substituted)) {
					continue;
				}
				if (removeElementInfo != null
						&& dependsOnAny(substituted, removeElementInfo.getRemovedElements())) {
					// don't add anything that is currently being removed or depends on it
					continue;
				}
				assert removeElementInfo == null
						|| !dependsOnAny(substituted, removeElementInfo.getRemovedElements());
				/*
				 * dropped this assertion since because of set constraints we also need elements that do not depend on
				 * a weq var
				 */
//				assert dependsOnAny(substituted, elemsToKeep);
				mManager.addElement(copy, substituted, true, false);
				worklist.add(substituted);
			}
			/*
			 * check literal constraints on current element, elements related to an elemToKeep this way must also be
			 * kept
			 */
			for (final ELEM relEl :
				copy.getLiteralSetConstraints().getRelatedElements(copy.getRepresentativeElement(current))) {
				if (visitedEquivalenceClassElements.contains(relEl)) {
					continue;
				}
				if (elemsInConstraintsToKeep.contains(relEl)) {
					continue;
				}
				if (removeElementInfo != null
						&& dependsOnAny(relEl, removeElementInfo.getRemovedElements())) {
					// don't add anything that is currently being removed or depends on it
					continue;
				}
				assert removeElementInfo == null
						|| !dependsOnAny(relEl, removeElementInfo.getRemovedElements());
//				assert dependsOnAny(relEl, elemsToKeep);
				mManager.addElement(copy, relEl, true, false);
				worklist.add(relEl);
			}
		}
		// TVER does not know about parent/child relationship of nodes, so it is safe
		final ThreeValuedEquivalenceRelation<ELEM> newTver =
				copy.mElementTVER.filterAndKeepOnlyConstraintsThatIntersectWith(elemsInConstraintsToKeep);
		assert assertNoNewElementsIntroduced(this.getAllElements(), newTver.getAllElements(), elemsToKeep)
			: "no elements may have been introduced that were not present before this operation";


		final CCLiteralSetConstraints<ELEM> newLiteralSetConstraints =
				copy.mLiteralSetConstraints.filterAndKeepOnlyConstraintsThatIntersectWith(elemsInConstraintsToKeep);

		/* Set constraints that are kept due to elemsInConstraintsToKeep may refer to elements that are not kept due to
		 * equality or disequality constraints. Thus we must add them to newTver in order to ensure the invariant that
		 * all elements in a set constraint are known to the enclosing congruenceClosure. */
		for (final ELEM elem : newLiteralSetConstraints.getAllElementsMentionedInASetConstraint()) {
			newTver.addElement(elem);
		}

		/*(former BUG!!!) this constructor may not add all child elements for all remaining elements, therefore
		 *  we either need a special constructor or do something else.. */
		final CongruenceClosure<ELEM> result = mManager.getCongruenceClosureFromTver(newTver, removeElementInfo,
				newLiteralSetConstraints, true);
		assert assertNoNewElementsIntroduced(this.getAllElements(), result.getAllElements(), elemsToKeep)
			: "no elements may have been introduced that were not present before this operation";
		assert !result.isInconsistent() : "cannot go from a consistent input to an inconsisten output during projectTo";
		return result;
	}

	/**
	 * projectToElements may only introduce fresh elements that depend on one of the elemsToKeep
	 *
	 * @param result
	 * @param elemsToKeep
	 * @return
	 */
	public boolean assertNoNewElementsIntroduced(final Set<ELEM> oldElems, final Set<ELEM> newElems,
			final Set<ELEM> elemsToKeep) {
		final Set<ELEM> diff = DataStructureUtils.difference(newElems, oldElems);
		for (final ELEM d : diff) {
			if (!dependsOnAny(d, elemsToKeep)) {
				assert false;
				return false;
			}
		}
//		if (!diff.isEmpty()) {
//			assert false;
//			return false;
//		}
		return true;
	}

	public Collection<ELEM> getAllRepresentatives() {
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
		if (sub.contains(elem)) {
			return true;
		}

		if (elem.isDependentNonFunctionApplication()) {
			if (DataStructureUtils.haveNonEmptyIntersection(elem.getSupportingNodes(), sub)) {
				return true;
			}
		}
		if (elem.isFunctionApplication()) {
			return dependsOnAny(elem.getAppliedFunction(), sub) || dependsOnAny(elem.getArgument(), sub);
		}
		return false;
	}

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

			for (final Entry<ELEM, ELEM> en : new HashRelation<>(mNodeToDependents).getSetOfPairs()) {
				mNodeToDependents.removePair(en.getKey(), en.getValue());
				mNodeToDependents.addPair(elemTransformer.apply(en.getKey()),
						elemTransformer.apply(en.getValue()));
			}
		}

		public Set<Entry<ELEM, ELEM>> getNodeToDependentPairs() {
			return mNodeToDependents.getSetOfPairs();
		}

		public Set<ELEM> getDependentsOf(final ELEM elem) {
			return mNodeToDependents.getImage(elem);
		}

		public void removeFromNodeToDependents(final ELEM etr) {
			if (etr.isDependentNonFunctionApplication()) {
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

	/**
	 * only used for technical reasons, to make mElementTVER inconsistent, don't use for anything else!
	 *
	 * @param node1
	 * @param node2
	 */
	public void reportDisequalityToElementTver(final ELEM node1, final ELEM node2) {
		mElementTVER.reportDisequality(node1, node2);

	}

	public Collection<ELEM> getArgCcPars(final ELEM elem) {
		return mAuxData.getArgCcPars(elem);
	}

	public Collection<ELEM> getFuncAppsWithFunc(final ELEM func) {
		return mFaAuxData.getAfParents(func);
	}

	public void setElementCurrentlyBeingRemoved(final IRemovalInfo<ELEM> re) {
		assert re == null || mElementCurrentlyBeingRemoved == null;
		mElementCurrentlyBeingRemoved = re;
	}

	@Override
	public boolean isDebugMode() {
		return mManager.isDebugMode();
	}

	@Override
	public ILogger getLogger() {
		return mManager.getLogger();
	}

	public Set<ELEM> getEquivalenceClass(final ELEM elem) {
		return Collections.unmodifiableSet(mElementTVER.getEquivalenceClass(elem));
	}

	public Set<ELEM> getAllLiterals() {
		return Collections.unmodifiableSet(mAllLiterals);
	}

	public CcManager<ELEM> getManager() {
		return mManager;
	}

	@Override
	public void reportContainsConstraint(final ELEM elem, final Set<ELEM> literalSet) {
		final HashRelation<ELEM, ELEM> eqToProp = mLiteralSetConstraints.reportContains(elem, literalSet);
		if (eqToProp != null) {
			for (final Entry<ELEM, ELEM> en : eqToProp) {
				mManager.reportEquality(en.getKey(), en.getValue(), this, true);
			}
		}
	}

	public void reportContainsConstraint(final ELEM elem, final Collection<SetConstraint<ELEM>> setCc) {
		final HashRelation<ELEM, ELEM> eqToProp = mLiteralSetConstraints.reportContains(elem, new HashSet<>(setCc));
		if (eqToProp != null) {
			for (final Entry<ELEM, ELEM> en : eqToProp) {
				mManager.reportEquality(en.getKey(), en.getValue(), this, true);
			}
		}
	}

	public Set<SetConstraint<ELEM>> getContainsConstraintForElement(final ELEM elem) {
		final Set<SetConstraint<ELEM>> constraint = mLiteralSetConstraints.getConstraint(elem);
		if (SetConstraintManager.isTautologicalWrtElement(elem, constraint)) {
			// normalization: if the constraint is tautological for the given element, return null instead
			return null;
		}
		return constraint;
	}
}
