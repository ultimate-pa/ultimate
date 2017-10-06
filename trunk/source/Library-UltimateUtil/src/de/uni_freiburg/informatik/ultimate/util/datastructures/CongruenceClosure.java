package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

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
 * TODO: can we make this more lightweight somehow? Maybe by initializing maps on demand? --> analyze..
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ELEM>
 *            The element type. Elements correspond to the "nodes" or terms in
 *            standard congruence closure terminology. Elements can be constants
 *            or function applications.
 */
public class CongruenceClosure<ELEM extends ICongruenceClosureElement<ELEM>> {

	protected final ThreeValuedEquivalenceRelation<ELEM> mElementTVER;

	protected final CongruenceClosure<ELEM>.CcAuxData mAuxData;

	protected final CongruenceClosure<ELEM>.FuncAppTreeAuxData mFaAuxData;

	protected final Collection<ELEM> mAllLiterals;

	/**
	 *
	 */
	boolean mConstructorInitializationPhase = false;

	/**
	 * Store which element we are currently in the process of removing (a remove can trigger deep recursive calls, and
	 *  some need to know this. Also sanity checks may be done more precisely when we know this)
	 */
	protected RemovalInfo mElementCurrentlyBeingRemoved;

	/**
	 * Constructs CongruenceClosure instance without any equalities or
	 * disequalities.
	 */
	public CongruenceClosure() {
		mElementTVER = new ThreeValuedEquivalenceRelation<>(CongruenceClosure::literalComparator);
		mAuxData = new CcAuxData();
		mFaAuxData = new FuncAppTreeAuxData();
		mAllLiterals = new HashSet<>();
	}

	/**
	 * Constructs CongruenceClosure instance that is in an inconsistent state from
	 * the beginning.
	 *
	 * @param isInconsistent dummy parameter separating this constructor from the one for the empty CongruenceClosure;
	 * 	  	must always be "true".
	 */
	public CongruenceClosure(final boolean isInconsistent) {
		if (!isInconsistent) {
			throw new AssertionError("use other constructor");
		}

		mElementTVER = null;
		mAuxData = null;
		mFaAuxData = null;
		mAllLiterals = null;
	}

	public CongruenceClosure(final ThreeValuedEquivalenceRelation<ELEM> newElemPartition) {
		mElementTVER = newElemPartition;
		mAuxData = new CcAuxData();
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
	 * Copy constructor.
	 *
	 * @param original the CC to copy
	 */
	public CongruenceClosure(final CongruenceClosure<ELEM> original) {
		if (original.isInconsistent()) {
			throw new IllegalArgumentException("use other constructor!");
		}
		mElementTVER = new ThreeValuedEquivalenceRelation<>(original.mElementTVER);
		mAuxData = new CcAuxData(original.mAuxData);
		mFaAuxData = new FuncAppTreeAuxData(original.mFaAuxData);
		mAllLiterals = new HashSet<>(original.mAllLiterals);
//		assert sanityCheck(); // can be violated during remove
	}

	public boolean reportEquality(final ELEM elem1, final ELEM elem2) {
		final boolean result = reportEqualityRec(elem1, elem2);
		assert sanityCheck();
		return result;
	}

	protected boolean reportEqualityRec(final ELEM elem1, final ELEM elem2) {
		if (isInconsistent()) {
			throw new IllegalStateException();
		}

		boolean freshElem = false;
		freshElem |= addElementRec(elem1);
		freshElem |= addElementRec(elem2);
		assert atMostOneLiteralPerEquivalenceClass();

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
		assert atMostOneLiteralPerEquivalenceClass();
		return true;
	}

	public boolean atMostOneLiteralPerEquivalenceClass() {
		if (isInconsistent()) {
			return true;
		}
		for (final Set<ELEM> eqc : mElementTVER.getAllEquivalenceClasses()) {
			assert eqc.stream().filter(e -> e.isLiteral()).collect(Collectors.toList()).size() < 2;
		}
		return true;
	}

	protected void doFwccAndBwccPropagationsFromMerge(
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

	protected Pair<HashRelation<ELEM, ELEM>, HashRelation<ELEM, ELEM>> doMergeAndComputePropagations(final ELEM elem1,
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
				mAuxData.updateAndGetPropagationsOnMerge(elem1, elem2, e1OldRep, e2OldRep, oldUnequalRepsForElem1,
						oldUnequalRepsForElem2);
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

	public boolean reportDisequality(final ELEM elem1, final ELEM elem2) {
		final boolean result = reportDisequalityRec(elem1, elem2);
		assert sanityCheck();
		return result;
	}

	protected boolean reportDisequalityRec(final ELEM elem1, final ELEM elem2) {
		assert elem1.hasSameTypeAs(elem2);

		if (isInconsistent()) {
			throw new IllegalStateException();
		}

		boolean freshElem = false;
		freshElem |= addElementRec(elem1);
		freshElem |= addElementRec(elem2);

		if (!freshElem && getEqualityStatus(elem1, elem2) == EqualityStatus.NOT_EQUAL) {
			// nothing to do
			return false;
		}


		mElementTVER.reportDisequality(elem1, elem2);
		if (mElementTVER.isInconsistent()) {
			return true;
		}

		final HashRelation<ELEM, ELEM> propDeqs = mAuxData.getPropagationsOnReportDisequality(elem1, elem2);

		for (final Entry<ELEM, ELEM> deq : propDeqs) {
			reportDisequalityRec(deq.getKey(), deq.getValue());
		}

		return true;
	}

	/**
	 *
	 * @param elem
	 * @return true iff the element was not known to this CongruenceClosure before
	 */
	protected boolean addElement(final ELEM elem) {
		final boolean result = addElementRec(elem);
		assert sanityCheck();
		return result;
	}

	protected boolean addElementRec(final ELEM elem) {
//		assert mElementCurrentlyBeingRemoved == null
//				|| !elem.isFunctionApplication()
//				|| (!elem.getAppliedFunction().equals(mElementCurrentlyBeingRemoved.getElem())
//						&& !elem.getArgument().equals(mElementCurrentlyBeingRemoved.getElem()));

		final boolean newlyAdded = mElementTVER.addElement(elem);
		if (newlyAdded) {
			registerNewElement(elem);
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
	protected void registerNewElement(final ELEM elem) {
		if (elem.isLiteral()) {
			mAllLiterals.add(elem);
		}

		if (!elem.isFunctionApplication()) {
			// nothing to do
			assert mElementTVER.getRepresentative(elem) != null : "this method assumes that elem has been added "
					+ "already";
//			assert sanityCheck();
			return;
		}


		mFaAuxData.addAfParent(elem.getAppliedFunction(), elem);
		mFaAuxData.addArgParent(elem.getArgument(), elem);

		/*
		 *  must come after the addElement calls for the children because it queries for their representative
		 *  (could be circumvented, I suppose..)
		 */
		final HashRelation<ELEM, ELEM> equalitiesToPropagate = mAuxData.registerNewElement(elem);

		addElementRec(elem.getAppliedFunction());
		addElementRec(elem.getArgument());



		for (final Entry<ELEM, ELEM> eq : equalitiesToPropagate.entrySet()) {
			reportEqualityRec(eq.getKey(), eq.getValue());
		}

//		assert sanityCheck();
	}

	public ELEM getRepresentativeAndAddElementIfNeeded(final ELEM elem) {
		addElement(elem);
		return mElementTVER.getRepresentative(elem);
	}

	public ELEM getRepresentativeElement(final ELEM elem) {
		final ELEM result = mElementTVER.getRepresentative(elem);
		if (result == null) {
			throw new IllegalArgumentException(
					"Use this method only for elements that you now have been added " + "already");
		}
		return result;

	}

	/**
	 * Remove a simple element, i.e., an element that is not a function application.
	 *
	 * @param elem
	 * @return
	 */
	public boolean removeSimpleElement(final ELEM elem) {
		return removeSimpleElementWithReplacementPreference(elem, null);
	}

	/**
	 * Remove a simple element, i.e., an element that is not a function application.
	 *
	 * During removal, CongruenceClosure attempts to add nodes in order to retain constraints that follow from the
	 * constraint but were not explicit before.
	 * The second parameter allows to give a set of preferred nodes to be chosen for this purpose if possible.
	 * Example:
	 * <li> state before this method call: {i, j, q} {a[i], x}
	 * <li> call this method with elem = i
	 * <li> we will have to remove a[i], too, thus the second partition block would be removed, thus without adding
	 *   nodes we would arrive at {j, q}
	 * <li> if we introduce a[j] (or a[q]) before removing a[i], we still have a[j] = x (a[q] = x), the result would be
	 *   {j, q}{a[j]=x}
	 * <li> giving q as a preferred replacement would enforce that we choose a[q] for this purpose, the result would be
	 *   {j, q}{a[q]=x}
	 *
	 * @param elem
	 * @param preferredReplacements
	 * @return
	 */
	public boolean removeSimpleElementWithReplacementPreference(final ELEM elem, final Set<ELEM> preferredReplacements) {
		// TODO Auto-generated method stub
		if (elem.isFunctionApplication()) {
				throw new IllegalArgumentException();
		}
		if (isInconsistent()) {
			throw new IllegalStateException();
		}
		if (!hasElement(elem)) {
			return false;
		}

		// TODO: seems ugly, but WeqCongruenceClosure need this field, too..
		if (this.getClass().equals(CongruenceClosure.class)) {
			assert mElementCurrentlyBeingRemoved == null;
			mElementCurrentlyBeingRemoved = new RemovalInfo(elem,
					getOtherEquivalenceClassMember(elem, preferredReplacements));
		}

		final boolean result = removeAnyElement(elem, null, preferredReplacements);

		if (this.getClass().equals(CongruenceClosure.class)) {
			mElementCurrentlyBeingRemoved = null;
		}

		return result;
	}

	protected final Map<ELEM, ELEM> removeSimpleElementTrackNewReps(final ELEM elem) {
		if (elem.isFunctionApplication()) {
			throw new IllegalArgumentException();
		}
		if (isInconsistent()) {
			throw new IllegalStateException();
		}
		if (!hasElement(elem)) {
			return new HashMap<>();
		}

		// TODO: seems ugly
		if (this.getClass().equals(CongruenceClosure.class)) {
			assert mElementCurrentlyBeingRemoved == null;
			mElementCurrentlyBeingRemoved = new RemovalInfo(elem, getOtherEquivalenceClassMember(elem, null));
		}

		final HashMap<ELEM, ELEM> removedElemToNewRep = new HashMap<>();
		removeAnyElement(elem, removedElemToNewRep, null);

		if (this.getClass().equals(CongruenceClosure.class)) {
			mElementCurrentlyBeingRemoved = null;
		}

		return removedElemToNewRep;
	}

	/**
	 * Helper (the division into removeSimple and removeFuncApp is used for subclasses)
	 *
	 * @param elem
	 * @param allWeqNodes
	 * @return
	 */
	private boolean removeAnyElement(final ELEM elem, final Map<ELEM, ELEM> removedElemToNewRep,
			final Set<ELEM> preferredReplacements) {
		if (!hasElement(elem)) {
			return false;
		}

		addNodesEquivalentToNodesWithRemovedElement(elem, preferredReplacements);
//		assert sanityCheckOnlyCc();

		final Collection<ELEM> oldAfParents = new ArrayList<>(mFaAuxData.getAfParents(elem));
		final Collection<ELEM> oldArgParents = new ArrayList<>(mFaAuxData.getArgParents(elem));

		if (removedElemToNewRep == null) {
			updateElementTverAndAuxDataOnRemoveElement(elem);
		} else {
			final ELEM newRep = updateElementTverAndAuxDataOnRemoveElement(elem);
			removedElemToNewRep.put(elem, newRep);
		}
		assert elementIsFullyRemovedOnlyCc(elem);
//		assert sanityCheckOnlyCc();

		for (final ELEM parent : oldAfParents) {
			removeAnyElement(parent, removedElemToNewRep, preferredReplacements);
		}
		for (final ELEM parent : oldArgParents) {
			removeAnyElement(parent, removedElemToNewRep, preferredReplacements);
		}
//		removeParents(oldAfParents, oldArgParents);

//		assert sanityCheckOnlyCc();
		assert elementIsFullyRemovedOnlyCc(elem);
		return true;
	}

	protected ELEM replaceWithOtherRepIfNecessaryAndPossible(final ELEM elem) {
		if (mElementCurrentlyBeingRemoved == null) {
			assert hasElement(elem);
			return elem;
		}
//		if (elem.equals(mElementCurrentlyBeingRemoved.getElem())) {
//		if (mElementCurrentlyBeingRemoved.supports(elem)) {
		if (supports(mElementCurrentlyBeingRemoved.getElem(), elem)) {

			final ELEM replacement = replace(elem, mElementCurrentlyBeingRemoved);

//			if (mElementCurrentlyBeingRemoved.getOtherRep() != null) {
//				assert hasElement(mElementCurrentlyBeingRemoved.getOtherRep());
//				return mElementCurrentlyBeingRemoved.getOtherRep();
			if (replacement != null && hasElement(replacement)) {
//				assert hasElement(replacement);
				return replacement;
			} else {
				return null;
			}
		}
		assert hasElement(elem);
		return elem;
	}

	/**
	 * elem depends on elementCurrentlyBeingRemoved.getElem()
	 *
	 * Attempt to replace elementCurrentlyBeingRemoved.getElem() by  elementCurrentlyBeingRemoved.getOtherElem()
	 * in elem.
	 *
	 * return null if not possible
	 *
	 *
	 * @param elem
	 * @param elementCurrentlyBeingRemoved
	 * @return
	 */
	protected ELEM replace(final ELEM elem, final CongruenceClosure<ELEM>.RemovalInfo elementCurrentlyBeingRemoved) {
		if (elementCurrentlyBeingRemoved == null) {
			return elem;
		}
		if (!supports(elementCurrentlyBeingRemoved.getElem(), elem)) {
			return elem;
		}

		if (elem.equals(elementCurrentlyBeingRemoved.getElem())) {
			return elementCurrentlyBeingRemoved.getOtherRep();
		}
		if (elem.isFunctionApplication()) {

			final ELEM afReplaced = replace(elem.getAppliedFunction(), elementCurrentlyBeingRemoved);
			if (afReplaced == null) {
				return null;
			}
			final ELEM argReplaced = replace(elem.getArgument(), elementCurrentlyBeingRemoved);
			if (argReplaced == null) {
				return null;
			}

			ELEM result = elem.replaceAppliedFunction(afReplaced);
			result = result.replaceArgument(argReplaced);

			return result;
		}
		return null;
	}

//	/**
//	 * Remove an element that is a function application.
//	 *
//	 * @param elem
//	 */
//	protected boolean removeFuncAppElement(final ELEM elem) {
//		if (!elem.isFunctionApplication()) {
//			throw new IllegalArgumentException();
//		}
//		return removeAnyElement(elem);
//	}

//	/**
//	 * remove elements that have elem as an argument
//	 */
//	protected void removeParents(final Collection<ELEM> oldAfParents, final Collection<ELEM> oldArgParents) {
//		for (final ELEM parent : oldAfParents) {
//			removeFuncAppElement(parent);
//		}
//		for (final ELEM parent : oldArgParents) {
//			removeFuncAppElement(parent);
//		}
//	}

	/**
	 * Does elem2 depend on elem?
	 *
	 * @param elem
	 * @param elem2
	 * @return
	 */
	protected boolean supports(final ELEM elem, final ELEM elem2) {
		return hasSubElement(elem2, Collections.singleton(elem));
	}

	protected ELEM updateElementTverAndAuxDataOnRemoveElement(final ELEM elem) {
		final boolean elemWasRepresentative = mElementTVER.isRepresentative(elem);

		final ELEM newRep = mElementTVER.removeElement(elem);

		mAuxData.removeElement(elem, elemWasRepresentative, newRep);
		if (elem.isFunctionApplication()) {
			mFaAuxData.removeAfParent(elem.getAppliedFunction(), elem);
			mFaAuxData.removeArgParent(elem.getArgument(), elem);
		}
		return newRep;
	}

	/**
	 * before removing the parents:
	 * if there is a newRep, insert a node where the subnode elem is replaced by newRep
	 * (this may introduce fresh nodes!)
	 *
	 * @param elem the element we are about to remove
	 * @param preferredReplacements
	 */
	protected void addNodesEquivalentToNodesWithRemovedElement(final ELEM elem, final Set<ELEM> preferredReplacements) {
		final ELEM otherRep = getOtherEquivalenceClassMember(elem, preferredReplacements);
		if (otherRep != null) {
			for (final ELEM parent : new ArrayList<>(mFaAuxData.getAfParents(elem))) {
				assert parent.getAppliedFunction() == elem;
				final ELEM replaced = parent.replaceAppliedFunction(otherRep);
				addElementRec(replaced);
			}
			for (final ELEM parent : new ArrayList<>(mFaAuxData.getArgParents(elem))) {
				assert parent.getArgument() == elem;
				final ELEM replaced = parent.replaceArgument(otherRep);
				addElementRec(replaced);
			}
		}
	}

	/**
	 * If elem is alone in its equivalence class, return null.
	 * Otherwise return any element from elem's equivalence class that is not elem.
	 *
	 * The user may specify a preference, i.e., if some element from the given set can be picked, it is picked.
	 *
	 * @param elem
	 * @param preferredReplacements
	 * @return
	 */
	protected ELEM getOtherEquivalenceClassMember(final ELEM elem, final Set<ELEM> preferredReplacements) {
		assert hasElement(elem);
		final Set<ELEM> eqc = mElementTVER.getEquivalenceClass(elem);
		if (eqc.size() == 1) {
			return null;
		}
		if (preferredReplacements != null) {
			final Optional<ELEM> preferred = eqc.stream()
					.filter(e ->  !e.equals(elem) && preferredReplacements.contains(e)).findFirst();
			if (preferred.isPresent()) {
				return preferred.get();
			}
		}
		return eqc.stream().filter(e -> !e.equals(elem)).findFirst().get();
//		return eqc.stream().filter(e -> e != elem).findAny().get();
	}

	protected boolean elementIsFullyRemoved(final ELEM elem) {
		return elementIsFullyRemovedOnlyCc(elem);
	}

	/**
	 * Checks  for any remainig entries of elem, does not look for subterms.
	 * @param elem
	 * @return
	 */
	protected boolean elementIsFullyRemovedOnlyCc(final ELEM elem) {
		if (mElementTVER.getRepresentative(elem) != null) {
			assert false;
			return false;
		}
		return true;
	}

	public CongruenceClosure<ELEM> join(final CongruenceClosure<ELEM> other) {
		if (this.isInconsistent()) {
			return new CongruenceClosure<>(other);
		}
		if (other.isInconsistent()) {
			return new CongruenceClosure<>(this);
		}

		final CongruenceClosure<ELEM> thisAligned = this.alignElementsAndFunctions(other);
		final CongruenceClosure<ELEM> otherAligned = other.alignElementsAndFunctions(this);

		final ThreeValuedEquivalenceRelation<ELEM> newElemTver = thisAligned.mElementTVER
				.join(otherAligned.mElementTVER);

		return new CongruenceClosure<>(newElemTver);
	}

	/**
	 * returns a copy of this where all elements and functions from other have been added.
	 * @param other
	 * @return
	 */
	protected CongruenceClosure<ELEM> alignElementsAndFunctions(final CongruenceClosure<ELEM> other) {
		assert !this.isInconsistent() && !other.isInconsistent();
//		if (isInconsistent()) {
//			return new CongruenceClosure<>(true);
//		}
//		if (other.isInconsistent()) {
//			// nothing to align to
//			return new CongruenceClosure<>(this);
//		}

//		assert this.sanityCheckOnlyCc();
		final CongruenceClosure<ELEM> result = new CongruenceClosure<>(this);
//		assert result.sanityCheckOnlyCc();

		other.getAllElements().stream().forEach(result::addElementRec);

//		assert result.sanityCheckOnlyCc();
		return result;
	}

	public CongruenceClosure<ELEM> meet(final CongruenceClosure<ELEM> other) {
		assert this.sanityCheckOnlyCc();
		assert other.sanityCheckOnlyCc();

		final CongruenceClosure<ELEM> result = meetRec(other);

		assert result.sanityCheckOnlyCc();
		return result;
	}

	/**
	 * Returns a new CongruenceClosure instance that is the meet of "this" and "other".
	 *
	 * @param other
	 * @return
	 */
	public CongruenceClosure<ELEM> meetRec(final CongruenceClosure<ELEM> other) {

		if (this.isInconsistent() || other.isInconsistent()) {
			return new CongruenceClosure<>(true);
		}

		final CongruenceClosure<ELEM> result = naiveMeet(other);
		assert result.atMostOneLiteralPerEquivalenceClass();

		if (result.isInconsistent()) {
			return new CongruenceClosure<>(true);
		}
		return result;
	}

	private CongruenceClosure<ELEM> naiveMeet(final CongruenceClosure<ELEM> other) {
		assert !this.isInconsistent() && !other.isInconsistent();

		final CongruenceClosure<ELEM> thisAligned = this.alignElementsAndFunctions(other);
		final CongruenceClosure<ELEM> otherAligned = other.alignElementsAndFunctions(this);

		for (final Entry<ELEM, ELEM> eq : otherAligned.getSupportingElementEqualities().entrySet()) {
			if (thisAligned.isInconsistent()) {
				return new CongruenceClosure<>(true);
			}
			thisAligned.reportEqualityRec(eq.getKey(), eq.getValue());
		}
		for (final Entry<ELEM, ELEM> deq : otherAligned.getElementDisequalities()) {
			if (thisAligned.isInconsistent()) {
				return new CongruenceClosure<>(true);
			}
			thisAligned.reportDisequalityRec(deq.getKey(), deq.getValue());
		}
		return thisAligned;
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
		final CongruenceClosure<ELEM> thisAligned = this.alignElementsAndFunctions(other);
		final CongruenceClosure<ELEM> otherAligned = other.alignElementsAndFunctions(this);
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
//		if (this.isInconsistent()) {
//			return true;
//		}
//		if (otherAligned.isInconsistent()) {
//			// we know this != False, and other = False
//			return false;
//		}

		assert thisAligned.getAllElements().equals(otherAligned.getAllElements());

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
			return false;
		}
		if (other.isInconsistent() || this.isInconsistent()) {
			return false;
		}

		final CongruenceClosure<ELEM> thisAligned = this.alignElementsAndFunctions(other);
		final CongruenceClosure<ELEM> otherAligned = other.alignElementsAndFunctions(this);
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
		for (final E rep : concatenateCollections(first.getAllRepresentatives(), second.getAllRepresentatives())) {
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

	public boolean vectorsAreCongruent(final List<ELEM> argList1, final List<ELEM> argList2) {
		for (int i = 0; i < argList1.size(); i++) {
			if (getEqualityStatus(argList1.get(i), argList2.get(i)) != EqualityStatus.EQUAL) {
				return false;
			}
		}
		return true;
	}


	protected boolean sanityCheck() {
		return sanityCheckOnlyCc();
	}

	/**
	 * Check for some class invariants.
	 *
	 * @return
	 */
	public boolean sanityCheckOnlyCc() {
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
		 * check that for each function application a[i], its representative's ccchild contains the corresponding
		 * af/arg-pair (a,i)
		 */
		for (final ELEM elem : getAllElements()) {
			if (!elem.isFunctionApplication()) {
				continue;
			}
			final ELEM rep = getRepresentativeElement(elem);
			if (!mAuxData.getCcChildren(rep).containsPair(elem.getAppliedFunction(), elem.getArgument())) {
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
			if (!afCcparFromDirectParents.equals(mAuxData.getAfCcPars(rep))) {
				assert false : "funcAppTreeAuxData and ccAuxData don't agree (Af case)";
				return false;
			}
			if (!argCcparFromDirectParents.equals(mAuxData.getArgCcPars(rep))) {
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
		if (getAllElements().size() < 20) {
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



	static <E> Collection<E> concatenateCollections(final Collection<E> c1, final Collection<E> c2) {
		final Collection<E> result = getFreshCollection(c1, c1.size() + c2.size());
		result.addAll(c2);
		return result;
	}

	static <E> Collection<E> getFreshCollection(final Collection<E> oldCollection, final int capacity) {
		final Collection<E> newCollection = new ArrayList<>(capacity);
		newCollection.addAll(oldCollection);
		return newCollection;
	}

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
//		assert sanitizeTransformer(elemTransformer, getAllElements()) : "we assume that the transformer does not "
//				+ "produce elements that were in the relation before!";

		mElementTVER.transformElements(elemTransformer);
		mAuxData.transformElements(elemTransformer);
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
		return mElementTVER.isConstrained(elem);
	}

	/**
	 * Returns a new CongruenceClosure which contains only those constraints in this CongruenceClosure that constrain
	 *  the given element.
	 * @param set
	 * @return
	 */
	public CongruenceClosure<ELEM> projectToElements(final Set<ELEM> set) {
		/*
		 *  we need to augment the set such that all equivalent elements are contained, too.
		 *  example:
		 *   we project to {q}
		 *   current partition: {q, i} {a[i], 0}
		 *   then the second block implicitly puts a constraint on q, too, thus we need to keep it.
		 */
		final HashSet<ELEM> augmentedSet = new HashSet<>();
		for (final ELEM e : set) {
			if (hasElement(e)) {
				augmentedSet.addAll(mElementTVER.getEquivalenceClass(e));
			}
		}

		// collect all elements that contain an element from the given set as a sub-node (i.e. child/descendant)
		final Set<ELEM> elemsWithSubFromSet =
				getAllElements().stream().filter(e -> hasSubElement(e, augmentedSet)).collect(Collectors.toSet());

		final ThreeValuedEquivalenceRelation<ELEM> newTver =
				mElementTVER.filterAndKeepOnlyConstraintsThatIntersectWith(elemsWithSubFromSet);

		return new CongruenceClosure<>(newTver);
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
	public static <ELEM extends ICongruenceClosureElement<ELEM>> boolean hasSubElement(final ELEM elem,
			final Set<ELEM> sub) {
		if (sub.contains(elem)) {
			return true;
		}
		if (elem.isFunctionApplication()) {
			return hasSubElement(elem.getAppliedFunction(), sub) || hasSubElement(elem.getArgument(), sub);
		}
		return false;
	}

	public boolean isRepresentative(final ELEM elem) {
		return mElementTVER.isRepresentative(elem);
	}

//	protected ELEM replaceFuncAppArgsWOtherRepIfNecAndPoss(final ELEM c) {
//		assert c.isFunctionApplication();
//		final ELEM cReplaced = c;
//
//		final ELEM afReplaced = replaceWithOtherRepIfNecessaryAndPossible(c.getAppliedFunction());
//		final ELEM argReplaced = replaceWithOtherRepIfNecessaryAndPossible(c.getArgument());
//		if (afReplaced == null || argReplaced == null) {
//			return null;
//		}
//		assert afReplaced == c.getAppliedFunction() || argReplaced == c.getArgument();
//		if (afReplaced != c.getAppliedFunction()) {
//			final ELEM rpaf = c.replaceAppliedFunction(mElementCurrentlyBeingRemoved.getOtherRep());
//			if (hasElement(rpaf)) {
//				return rpaf;
//			} else {
//				return null;
//			}
//		} else if (argReplaced != c.getArgument()) {
//			final ELEM rparg = c.replaceArgument(mElementCurrentlyBeingRemoved.getOtherRep());
//			if (hasElement(rparg)) {
//				return rparg;
//			} else {
//				return null;
//			}
//		}
//		return cReplaced;
//	}

	/**
	 * auxilliary data related to the tree where an edge a -> b means that b is an argument to function a
	 * (this is mostly/only needed for element removal)
	 */
	protected class FuncAppTreeAuxData {
		// these cannot be managed within the nodes because the nodes are shared between CongruenceClosure instances!
		private final HashRelation<ELEM, ELEM> mDirectAfPars;
		private final HashRelation<ELEM, ELEM> mDirectArgPars;

		FuncAppTreeAuxData() {
			mDirectAfPars = new HashRelation<>();
			mDirectArgPars = new HashRelation<>();
		}

		FuncAppTreeAuxData(final CongruenceClosure<ELEM>.FuncAppTreeAuxData faAuxData) {
			mDirectAfPars = new HashRelation<>(faAuxData.mDirectAfPars);
			mDirectArgPars = new HashRelation<>(faAuxData.mDirectArgPars);
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
		}
	}

	/**
	 * auxilliary data related to congruence classes
	 */
	protected class CcAuxData {

		private final HashRelation<ELEM, ELEM> mAfCcPars;
		private final HashRelation<ELEM, ELEM> mArgCcPars;

		private final Map<ELEM, HashRelation<ELEM, ELEM>> mCcChildren;

		/**
		 * normally we only allow get..(elem) calls when elem is a representative of the encolosing CongruenceClosure
		 * this flag deactivates those checks
		 */
		private final boolean mOmitRepresentativeChecks;

		CcAuxData() {
			mAfCcPars = new HashRelation<>();
			mArgCcPars = new HashRelation<>();
			mCcChildren = new HashMap<>();
			mOmitRepresentativeChecks = false;
		}

		public CcAuxData(final CcAuxData auxData, final boolean omitRepresentativeChecks) {
			mAfCcPars = new HashRelation<>(auxData.mAfCcPars);
			mArgCcPars = new HashRelation<>(auxData.mArgCcPars);
			mCcChildren = new HashMap<>();
			for (final Entry<ELEM, HashRelation<ELEM, ELEM>> en : auxData.mCcChildren.entrySet()) {
				mCcChildren.put(en.getKey(), new HashRelation<>(en.getValue()));
			}
			mOmitRepresentativeChecks = omitRepresentativeChecks;
		}

		CcAuxData(final CongruenceClosure<ELEM>.CcAuxData auxData) {
			this(auxData, false);
		}

		/**
		 * e1 and e2 are currently merged
		 * computes pairs of elements that must be merged as a consequence of merging e1 and e2, because of
		 * (forward) congruence
		 *
		 * @param e1
		 * @param e2
		 * @param oldUnequalRepsForElem2
		 * @param oldUnequalRepsForElem1
		 * @return
		 */
		Pair<HashRelation<ELEM, ELEM>, HashRelation<ELEM, ELEM>> updateAndGetPropagationsOnMerge(final ELEM e1,
				final ELEM e2, final ELEM e1OldRep, final ELEM e2OldRep, final Set<ELEM> oldUnequalRepsForElem1,
				final Set<ELEM> oldUnequalRepsForElem2) {

			final ELEM newRep = mElementTVER.getRepresentative(e1);
			assert mElementTVER.getRepresentative(e2) == newRep : "we merged before calling this method, right?";

			/*
			 * collect new equalities and disequalities
			 */
			final HashRelation<ELEM, ELEM> congruentResult = new HashRelation<>();
			final HashRelation<ELEM, ELEM> unequalResult = new HashRelation<>();

			final Set<ELEM> afccpar1 = mAfCcPars.getImage(e1OldRep);
			final Set<ELEM> afccpar2 = mAfCcPars.getImage(e2OldRep);

			final Set<ELEM> argccpar1 = mArgCcPars.getImage(e1OldRep);
			final Set<ELEM> argccpar2 = mArgCcPars.getImage(e2OldRep);

			collectCcParBasedPropagations(afccpar1, afccpar2, congruentResult, unequalResult);
			collectCcParBasedPropagations(argccpar1, argccpar2, congruentResult, unequalResult);
			assert hasOnlyPairsOfSameType(congruentResult);
			assert hasOnlyPairsOfSameType(unequalResult);

			collectPropagationsForImplicitlyAddedDisequalities(oldUnequalRepsForElem1, e2OldRep, unequalResult);
			collectPropagationsForImplicitlyAddedDisequalities(oldUnequalRepsForElem2, e1OldRep, unequalResult);
			assert hasOnlyPairsOfSameType(unequalResult);

			/*
			 * update ccPars, ccChildren entries
			 */
			if (newRep == e1OldRep) {
				final Set<ELEM> oldAf2 = mAfCcPars.removeDomainElement(e2OldRep);
				if (oldAf2 != null) {
					for (final ELEM e : oldAf2) {
						mAfCcPars.addPair(newRep, e);
					}
				}
				final Set<ELEM> oldArg2 = mArgCcPars.removeDomainElement(e2OldRep);
				if (oldArg2 != null) {
					for (final ELEM e : oldArg2) {
						mArgCcPars.addPair(newRep, e);
					}
				}
			} else {
				assert newRep == e2OldRep;
				final Set<ELEM> oldAf1 = mAfCcPars.removeDomainElement(e1OldRep);
				if (oldAf1 != null) {
					for (final ELEM e : oldAf1) {
						mAfCcPars.addPair(newRep, e);
					}
				}
				final Set<ELEM> oldArg1 = mArgCcPars.removeDomainElement(e1OldRep);
				if (oldArg1 != null) {
					for (final ELEM e : oldArg1) {
						mArgCcPars.addPair(newRep, e);
					}
				}
			}

			final HashRelation<ELEM, ELEM> newCcc = new HashRelation<>();
			final HashRelation<ELEM, ELEM> oldCcc1 = mCcChildren.remove(e1OldRep);
			if (oldCcc1 != null) {
				newCcc.addAll(oldCcc1);
			}
			final HashRelation<ELEM, ELEM> oldCcc2 = mCcChildren.remove(e2OldRep);
			if (oldCcc2 != null) {
				newCcc.addAll(oldCcc2);
			}
			mCcChildren.put(newRep, newCcc);

			assert hasOnlyPairsOfSameType(congruentResult);
			assert hasOnlyPairsOfSameType(unequalResult);
			return new Pair<>(congruentResult, unequalResult);
		}

		private boolean hasOnlyPairsOfSameType(final HashRelation<ELEM, ELEM> relation) {
			for (final Entry<ELEM, ELEM> pair : relation) {
				assert pair.getKey().hasSameTypeAs(pair.getValue()) : "relation should only have pairs of same type"
						+ "but does not";
			}
			return true;
		}

		private void collectCcParBasedPropagations(final Set<ELEM> parents1, final Set<ELEM> parents2,
				final HashRelation<ELEM, ELEM> congruentResult, final HashRelation<ELEM, ELEM> unequalResult) {
			if (parents1 == null || parents2 == null || parents1.isEmpty() || parents2.isEmpty()) {
				// nothing to do
				return;
			}

			for (final List<ELEM> parentPair :
				CrossProducts.crossProductOfSets(Arrays.asList(parents1, parents2))) {
				final ELEM parent1 = parentPair.get(0);
				final ELEM parent2 = parentPair.get(1);

				/*
				 * fwcc
				 *
				 * is it correct to do this with out the vectors, just with getAppliedFunction and getArgument?
				 */
				if (hasElements(parent1.getAppliedFunction(), parent1.getArgument(),
						parent2.getAppliedFunction(), parent2.getArgument())
						&& getEqualityStatus(parent1.getAppliedFunction(), parent2.getAppliedFunction())
						== EqualityStatus.EQUAL
						&& getEqualityStatus(parent1.getArgument(), parent2.getArgument())
						== EqualityStatus.EQUAL) {

					congruentResult.addPair(parent1, parent2);
					continue;
				}

				/*
				 * bwcc (1)
				 */
				if (getEqualityStatus(parent1, parent2) == EqualityStatus.NOT_EQUAL) {
					addPropIfOneIsEqualOneIsUnconstrained(parent1.getAppliedFunction(), parent1.getArgument(),
							parent2.getAppliedFunction(), parent2.getArgument(), unequalResult);
				}
			}
		}

		/**
		 * This method is a helper that, for two representatives of equivalence classes
		 * checks if, because of merging the two equivalence classes, any disequality
		 * propagations are possible.
		 *
		 * Example:
		 * <li>preState: (i = f(y)) , (j != f(x)), (i = j)
		 * <li>we just added an equality between i and j (did the merge operation)
		 * <li>one call of this method will be with (preState, i, f(x))
		 * <li>we will get the output state: (i = f(y)) , (j != f(x)), (i = j), (x != y)
		 *
		 * @param oldUnequalRepsForElem1
		 * @param e2OldRep
		 * @param e2OldRep
		 * @param oldCcChild
		 */
		private void collectPropagationsForImplicitlyAddedDisequalities(final Set<ELEM> oldUnequalRepsForElem1,
					final ELEM e2OldRep, final HashRelation<ELEM, ELEM> disequalitiesToPropagate) {

			for (final ELEM repUnequalToE1 : oldUnequalRepsForElem1) {
				final HashRelation<ELEM, ELEM> unequalRep1Cccs = mCcChildren.get(repUnequalToE1);
				if (unequalRep1Cccs == null) {
						continue;
				}
				for (final Entry<ELEM, ELEM> ccc2 : unequalRep1Cccs) {
					final HashRelation<ELEM, ELEM> mergePartnerOldRepCccs = mCcChildren.get(e2OldRep);
					if (mergePartnerOldRepCccs == null) {
						continue;
					}
					for (final Entry<ELEM, ELEM> ccc1 : mergePartnerOldRepCccs) {
						addPropIfOneIsEqualOneIsUnconstrained(ccc1.getKey(), ccc1.getValue(), ccc2.getKey(),
								ccc2.getValue(), disequalitiesToPropagate);
					}
				}
			}
		}

		public void removeElement(final ELEM elem, final boolean elemWasRepresentative, final ELEM newRep) {
			/*
			 * ccpar and ccchild only have representatives in their keySets
			 *  --> move the information to the new representative from elem, if necessary
			 */
			if (elemWasRepresentative) {
				final Set<ELEM> oldAfCcparEntry = mAfCcPars.removeDomainElement(elem);
				if (newRep != null && oldAfCcparEntry != null) {
					oldAfCcparEntry//.stream().filter(e -> !e.getAppliedFunction().equals(elem))
						.forEach(e -> mAfCcPars.addPair(newRep, e));
				}

				final Set<ELEM> oldArgCcparEntry = mArgCcPars.removeDomainElement(elem);
				if (newRep != null && oldArgCcparEntry != null) {
					oldArgCcparEntry//.stream().filter(e -> !e.getArgument().equals(elem))
						.forEach(e -> mArgCcPars.addPair(newRep, e));
				}

				final HashRelation<ELEM, ELEM> oldCccEntry = mCcChildren.remove(elem);
				if (newRep != null && oldCccEntry != null) {
					mCcChildren.put(newRep, oldCccEntry);
				}
			}

			/*
			 * remove ccpar entries that were there because of elem,
			 * for example if we have a partition block { i, j} with ccpar { f(i) } and we remove i, then f(i) must be
			 * eliminated from ccpar
			 */
			if (newRep != null) {
				for (final ELEM e : new ArrayList<>(mAfCcPars.getImage(newRep))) {
					if (e.getAppliedFunction().equals(elem)) {
						mAfCcPars.removePair(newRep, e);
					}
				}
				for (final ELEM e : new ArrayList<>(mArgCcPars.getImage(newRep))) {
					if (e.getArgument().equals(elem)) {
						mArgCcPars.removePair(newRep, e);
					}
				}
			}

			/*
			 * remove any entries of elem to one of the maps
			 *  possible optimization: look specifically for where elem could be instead of iterating over all pairs..
			 */
			mAfCcPars.removeRangeElement(elem);
			mArgCcPars.removeRangeElement(elem);

			if (newRep == null) {
				// there was no equal element to elem, we already removed elem from the keys in the above step
				assert elemWasRepresentative;
			} else {
				if (elem.isFunctionApplication()) {
					mCcChildren.get(newRep).removePair(elem.getAppliedFunction(), elem.getArgument());
				}
			}
		}

		HashRelation<ELEM, ELEM> registerNewElement(final ELEM elem) {
			assert elem.isFunctionApplication() : "right?..";

			final ELEM afRep = hasElement(elem.getAppliedFunction()) ?
					mElementTVER.getRepresentative(elem.getAppliedFunction()) :
						elem.getAppliedFunction();
			final ELEM argRep = hasElement(elem.getArgument()) ?
					mElementTVER.getRepresentative(elem.getArgument()) :
						elem.getArgument();


			final HashRelation<ELEM, ELEM> equalitiesToPropagate = new HashRelation<>();
			final Set<ELEM> afCcPars = mAfCcPars.getImage(afRep);
			final Set<ELEM> candidates = afCcPars.stream()
					.filter(afccpar ->
						(hasElement(argRep) &&
							hasElement(afccpar.getArgument()) &&
							getEqualityStatus(argRep, afccpar.getArgument()) == EqualityStatus.EQUAL)
						)
					.collect(Collectors.toSet());

			/*
			 * we have to make sure to not add an equality for propagation where an element contains the element
			 *  currently being removed EDIT: no we don't.. --> those might be the propagations for one of the elements
			 *  we added to conserve information..
			 */
			for (final ELEM c : candidates) {
				assert c.isFunctionApplication();
				equalitiesToPropagate.addPair(elem, c);

//				final ELEM cReplaced = replaceFuncAppArgsWOtherRepIfNecAndPoss(c);
//
//				if (cReplaced != null) {
//					equalitiesToPropagate.addPair(elem, cReplaced);
//				}
			}


//			assert mElementCurrentlyBeingRemoved == null
//					|| !equalitiesToPropagate.entrySet().stream().map(en -> en.getValue())
//						.anyMatch(c -> c.isFunctionApplication()
//					&& (c.getAppliedFunction().equals(mElementCurrentlyBeingRemoved.getElem())
//							|| c.getArgument().equals(mElementCurrentlyBeingRemoved.getElem())));

			mAfCcPars.addPair(afRep, elem);
			mArgCcPars.addPair(argRep, elem);

			// is it even possible that elem is not its own representative at this point??
			final ELEM elemRep = mElementTVER.getRepresentative(elem);

			updateCcChild(elemRep, elem.getAppliedFunction(), elem.getArgument());

			return equalitiesToPropagate;
		}

		private void updateCcChild(final ELEM elemRep, final ELEM appliedFunction, final ELEM argument) {
			HashRelation<ELEM, ELEM> elemCcc = mCcChildren.get(elemRep);
			if (elemCcc == null) {
				elemCcc = new HashRelation<>();
				mCcChildren.put(elemRep, elemCcc);
			}
			elemCcc.addPair(appliedFunction, argument);
		}

		public HashRelation<ELEM, ELEM> getPropagationsOnReportDisequality(final ELEM elem1, final ELEM elem2) {
			final HashRelation<ELEM, ELEM> result = new HashRelation<>();

			final ELEM e1Rep = mElementTVER.getRepresentative(elem1);
			final ELEM e2Rep = mElementTVER.getRepresentative(elem2);

			final HashRelation<ELEM, ELEM> ccc1 = getCcChildren(e1Rep);
			final HashRelation<ELEM, ELEM> ccc2 = getCcChildren(e2Rep);


			for (final Entry<ELEM, ELEM> pair1 : ccc1.entrySet()) {
				for (final Entry<ELEM, ELEM> pair2 : ccc2.entrySet()) {
					addPropIfOneIsEqualOneIsUnconstrained(pair1.getKey(), pair1.getValue(), pair2.getKey(),
							pair2.getValue(), result);
				}
			}
			return result;
		}

		public HashRelation<ELEM, ELEM> getCcChildren(final ELEM rep) {
			assert mOmitRepresentativeChecks || isRepresentative(rep);
			HashRelation<ELEM, ELEM> result = mCcChildren.get(rep);
			if (result == null) {
				result = new HashRelation<>();
				mCcChildren.put(rep, result);
			}
			return result;
		}

		private void addPropIfOneIsEqualOneIsUnconstrained(final ELEM af1, final ELEM arg1, final ELEM af2,
				final ELEM arg2,final HashRelation<ELEM, ELEM> result) {
			if (!hasElement(af1) || !hasElement(af2) || !hasElement(arg1) || !hasElement(arg2)) {
				/*
				 *  it may happen that during a remove element we reach here and some map still has an element that is
				 *  being removed (if we added a propagation here, we would add the element back..)
				 */
				return;
			}

			final EqualityStatus equalityStatusOfAppliedFunctions =
					getEqualityStatus(af1, af2);
			final EqualityStatus equalityStatusOfArguments =
					getEqualityStatus(arg1, arg2);

			if (equalityStatusOfAppliedFunctions == EqualityStatus.EQUAL
					&& equalityStatusOfArguments == EqualityStatus.UNKNOWN
					&& arg1.hasSameTypeAs(arg2)) {
				result.addPair(arg1, arg2);
			}

			if (equalityStatusOfAppliedFunctions == EqualityStatus.UNKNOWN
					&& equalityStatusOfArguments == EqualityStatus.EQUAL
					&& af1.hasSameTypeAs(af2)) {
				result.addPair(af1, af2);
			}
		}

		public Collection<ELEM> getAfCcPars(final ELEM elem) {
			assert mOmitRepresentativeChecks || isRepresentative(elem);
			return mAfCcPars.getImage(elem);
		}

		public Collection<ELEM> getArgCcPars(final ELEM elem) {
			assert mOmitRepresentativeChecks || isRepresentative(elem);
			return mArgCcPars.getImage(elem);
		}

		public void transformElements(final Function<ELEM, ELEM> elemTransformer) {
			mAfCcPars.transformElements(elemTransformer, elemTransformer);
			mArgCcPars.transformElements(elemTransformer, elemTransformer);

			for (final Entry<ELEM, HashRelation<ELEM, ELEM>> en : new HashMap<>(mCcChildren).entrySet()) {
				mCcChildren.remove(en.getKey());
				assert en.getValue().isEmpty() ||
					!mCcChildren.values().contains(en.getValue()) : "just to make sure there's no overlap in the "
						+ "map's image values";
				en.getValue().transformElements(elemTransformer, elemTransformer);
				mCcChildren.put(elemTransformer.apply(en.getKey()), en.getValue());
			}
		}
	}

	public class RemovalInfo {

		private final ELEM mElemBeingRemoved;
		private final ELEM mOtherRep;

		public RemovalInfo(final ELEM elemBeingRemoved, final ELEM otherRep) {
			assert !elemBeingRemoved.isFunctionApplication();
			mElemBeingRemoved = elemBeingRemoved;
			mOtherRep = otherRep;
		}

		public ELEM getElem() {
			return mElemBeingRemoved;
		}

		public ELEM getOtherRep() {
			return mOtherRep;
		}

		@Override
		public String toString() {
			return mElemBeingRemoved + " --> " + mOtherRep;
		}
	}

}
