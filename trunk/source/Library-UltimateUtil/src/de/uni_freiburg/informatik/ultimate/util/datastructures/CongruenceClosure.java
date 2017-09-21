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

	protected final CongruenceClosure<ELEM>.AuxData mAuxData;


	/**
	 * Constructs CongruenceClosure instance without any equalities or
	 * disequalities.
	 */
	public CongruenceClosure() {
		mElementTVER = new ThreeValuedEquivalenceRelation<>();
		mAuxData = new AuxData();
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
	}

	public CongruenceClosure(final ThreeValuedEquivalenceRelation<ELEM> newElemPartition) {
		mElementTVER = newElemPartition;
		mAuxData = new AuxData();

		// initialize the helper mappings according to mElementTVER
		for (final ELEM elem : new HashSet<>(mElementTVER.getAllElements())) {
			registerNewElement(elem);
		}
		assert sanityCheck();
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
		mAuxData = new AuxData(original.mAuxData);
		assert sanityCheck();
	}

	public boolean reportEquality(final ELEM elem1, final ELEM elem2) {
		if (isInconsistent()) {
			throw new IllegalStateException();
		}

		boolean freshElem = false;
		freshElem |= addElement(elem1);
		freshElem |= addElement(elem2);

		if (!freshElem && getEqualityStatus(elem1, elem2) == EqualityStatus.EQUAL) {
			// nothing to do
			return false;
		}
		if (!freshElem && getEqualityStatus(elem1, elem2) == EqualityStatus.NOT_EQUAL) {
			// report it to tver so that it is in an inconsistent state
			mElementTVER.reportEquality(elem1, elem2);
			return true;
		}

		final ELEM e1OldRep = mElementTVER.getRepresentative(elem1);
		final ELEM e2OldRep = mElementTVER.getRepresentative(elem2);

		mElementTVER.reportEquality(elem1, elem2);
		if (mElementTVER.isInconsistent()) {
			return true;
		}

		final Pair<HashRelation<ELEM, ELEM>, HashRelation<ELEM, ELEM>> propInfo =
				mAuxData.updateAndGetPropagationsOnMerge(elem1, elem2, e1OldRep, e2OldRep);
		final HashRelation<ELEM, ELEM> equalitiesToPropagate = propInfo.getFirst();
		final HashRelation<ELEM, ELEM> disequalitiesToPropagate = propInfo.getSecond();

		/*
		 * (fwcc)
		 */
		for (final Entry<ELEM, ELEM> congruentParents : equalitiesToPropagate) {
			reportEquality(congruentParents.getKey(), congruentParents.getValue());
		}

		/*
		 * (bwcc1), (bwcc2)  (-- they're only separate cases during reportDisequality)
		 */
		for (final Entry<ELEM, ELEM> unequalNeighborIndices : disequalitiesToPropagate) {
			reportDisequality(unequalNeighborIndices.getKey(), unequalNeighborIndices.getValue());
		}

		assert sanityCheck();
		return true;
	}

	public boolean reportDisequality(final ELEM elem1, final ELEM elem2) {
		if (isInconsistent()) {
			throw new IllegalStateException();
		}

		boolean freshElem = false;
		freshElem |= addElement(elem1);
		freshElem |= addElement(elem2);

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
			reportDisequality(deq.getKey(), deq.getValue());
		}

		assert sanityCheck();
		return true;
	}

	/**
	 *
	 * @param elem
	 * @return true iff the element was not known to this CongruenceClosure before
	 */
	protected boolean addElement(final ELEM elem) {
		final boolean newlyAdded = mElementTVER.addElement(elem);
		if (newlyAdded) {
			registerNewElement(elem);
		}
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
		assert sanityCheck();

		if (!elem.isFunctionApplication()) {
			// nothing to do
			assert mElementTVER.getRepresentative(elem) != null : "this method assumes that elem has been added "
					+ "already";
			return;
		}

		addElement(elem.getAppliedFunction());
		addElement(elem.getArgument());

		/*
		 *  must come after the addElement calls for the children because it queries for their representative
		 *  (could be circumvented, I suppose..)
		 */
		final HashRelation<ELEM, ELEM> equalitiesToPropagate = mAuxData.registerNewElement(elem);
		for (final Entry<ELEM, ELEM> eq : equalitiesToPropagate.entrySet()) {
			reportEquality(eq.getKey(), eq.getValue());
		}

		assert sanityCheck();
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

	public boolean removeElement(final ELEM elem) {
		if (isInconsistent()) {
			throw new IllegalStateException();
		}
		if (!hasElement(elem)) {
			return false;
		}

		final boolean elemWasRepresentative = mElementTVER.isRepresentative(elem);
		final ELEM newRep = mElementTVER.removeElement(elem);
		mAuxData.removeElement(elem, elemWasRepresentative, newRep);

		for (final ELEM parent : elem.getAfParents()) {
			removeElement(parent);
		}
		for (final ELEM parent : elem.getArgParents()) {
			removeElement(parent);
		}

		assert elementIsFullyRemoved(elem);
		return true;
	}

	/**
	 * Checks  for any remainig entries of elem, does not look for subterms.
	 * @param elem
	 * @return
	 */
	protected boolean elementIsFullyRemoved(final ELEM elem) {
		if (mElementTVER.getRepresentative(elem) != null) {
			assert false;
			return false;
		}
		return true;
	}

	public CongruenceClosure<ELEM> join(final CongruenceClosure<ELEM> other) {
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
		assert this.sanityCheck();
		final CongruenceClosure<ELEM> result = new CongruenceClosure<>(this);
		assert result.sanityCheck();

		other.getAllElements().stream().forEach(result::addElement);

		assert result.sanityCheck();
		return result;
	}

	/**
	 * Returns a new CongruenceClosure instance that is the meet of "this" and "other".
	 *
	 * @param other
	 * @return
	 */
	public CongruenceClosure<ELEM> meet(final CongruenceClosure<ELEM> other) {
		assert this.sanityCheck();
		assert other.sanityCheck();

		if (this.isInconsistent() || other.isInconsistent()) {
			return new CongruenceClosure<>(true);
		}

		final CongruenceClosure<ELEM> result = naiveMeet(other);
		if (result.isInconsistent()) {
			return new CongruenceClosure<>(true);
		}
		assert result.sanityCheck();
		return result;
	}

	private CongruenceClosure<ELEM> naiveMeet(final CongruenceClosure<ELEM> other) {
		final CongruenceClosure<ELEM> thisAligned = this.alignElementsAndFunctions(other);
		final CongruenceClosure<ELEM> otherAligned = other.alignElementsAndFunctions(this);

		for (final Entry<ELEM, ELEM> eq : otherAligned.getSupportingElementEqualities().entrySet()) {
			if (thisAligned.isInconsistent()) {
				return new CongruenceClosure<>(true);
			}
			thisAligned.reportEquality(eq.getKey(), eq.getValue());
		}
		for (final Entry<ELEM, ELEM> deq : otherAligned.getElementDisequalities()) {
			if (thisAligned.isInconsistent()) {
				return new CongruenceClosure<>(true);
			}
			thisAligned.reportDisequality(deq.getKey(), deq.getValue());
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
	 */
	private boolean checkIsStrongerThan(final CongruenceClosure<ELEM> thisAligned,
			final CongruenceClosure<ELEM> otherAligned) {
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
			if (mElementTVER.getEqualityStatus(argList1.get(i), argList2.get(i)) != EqualityStatus.EQUAL) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Check for some class invariants.
	 *
	 * @return
	 */
	protected boolean sanityCheck() {
		if (this.isInconsistent()) {
			if (mElementTVER != null) {
				// transitory CClosure instance which will later be replaced by the "bottom" variant
				if (!mElementTVER.isInconsistent()) {
					assert false;
					return false;
				}
			}
			return true;
		}

		if (mElementTVER.isInconsistent()) {
					assert false;
					return false;
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
					assert false;
					return false;
				}
			}
		}
		for (final Entry<ELEM, ELEM> deq : mElementTVER.getDisequalities()) {
			if (!deq.getKey().hasSameTypeAs(deq.getValue())) {
				assert false;
				return false;
			}
		}

		if (!isInconsistent()) {
			if (mElementTVER.isInconsistent()) {
				assert false;
				return false;
			}
			if (mElementTVER == null) {
				assert false;
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

	@Override
	public String toString() {
		if (isTautological()) {
			return "True";
		}
		if (isInconsistent()) {
			return "False";
		}

		final StringBuilder sb = new StringBuilder();

		sb.append("Element equivalences:");
		sb.append(mElementTVER);

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
		assert sanitizeTransformer(elemTransformer, getAllElements()) : "we assume that the transformer does not "
				+ "produce elements that were in the relation before!";

		mElementTVER.transformElements(elemTransformer);
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
		final ThreeValuedEquivalenceRelation<ELEM> newElemPartition =
				this.mElementTVER.projectToConstraintsWith(set);
		return new CongruenceClosure<>(newElemPartition);
	}

	public Collection<ELEM> getAllElementRepresentatives() {
		return mElementTVER.getAllRepresentatives();
	}

	public boolean isRepresentative(final ELEM elem) {
		return mElementTVER.isRepresentative(elem);
	}

	protected class AuxData {

		private final HashRelation<ELEM, ELEM> mAfCcPars;
		private final HashRelation<ELEM, ELEM> mArgCcPars;

		Map<ELEM, HashRelation<ELEM, ELEM>> mCcChildren = new HashMap<>();

		AuxData() {
			mAfCcPars = new HashRelation<>();
			mArgCcPars = new HashRelation<>();
		}

		AuxData(final CongruenceClosure<ELEM>.AuxData auxData) {
			mAfCcPars = new HashRelation<>(auxData.mAfCcPars);
			mArgCcPars = new HashRelation<>(auxData.mArgCcPars);
		}

		/**
		 * e1 and e2 are currently merged
		 * computes pairs of elements that must be merged as a consequence of merging e1 and e2, because of
		 * (forward) congruence
		 *
		 * @param e1
		 * @param e2
		 * @return
		 */
		Pair<HashRelation<ELEM, ELEM>, HashRelation<ELEM, ELEM>> updateAndGetPropagationsOnMerge(final ELEM e1,
				final ELEM e2, final ELEM e1OldRep, final ELEM e2OldRep) {

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

			collectPropagationsForImplicitlyAddedDisequalities(e1OldRep, unequalResult);
			collectPropagationsForImplicitlyAddedDisequalities(e2OldRep, unequalResult);

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

			return new Pair<>(congruentResult, unequalResult);
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
				if (getEqualityStatus(parent1.getAppliedFunction(), parent2.getAppliedFunction())
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
		 * @param e1OldRep
		 * @param e2OldRep
		 * @param oldCcChild
		 */
		private void collectPropagationsForImplicitlyAddedDisequalities(final ELEM e1OldRep,
					final HashRelation<ELEM, ELEM> disequalitiesToPropagate) {

			if (mCcChildren.get(e1OldRep) == null || mCcChildren.get(e1OldRep).isEmpty()) {
				return;
			}

			for (final ELEM repUnequalToE1 : mElementTVER.getRepresentativesUnequalTo(e1OldRep)) {

				for (final Entry<ELEM, ELEM> ccc1 : mCcChildren.get(e1OldRep)) {
					final HashRelation<ELEM, ELEM> unequalRepCccs = mCcChildren.get(repUnequalToE1);
					if (unequalRepCccs == null) {
						continue;
					}
					for (final Entry<ELEM, ELEM> ccc2 : unequalRepCccs) {
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
					oldAfCcparEntry.forEach(e -> mAfCcPars.addPair(newRep, e));
				}

				final Set<ELEM> oldArgCcparEntry = mArgCcPars.removeDomainElement(elem);
				if (newRep != null && oldArgCcparEntry != null) {
					oldArgCcparEntry.forEach(e -> mArgCcPars.addPair(newRep, e));
				}

				final HashRelation<ELEM, ELEM> oldCccEntry = mCcChildren.remove(elem);
				if (newRep != null && oldCccEntry != null) {
					mCcChildren.put(newRep, oldCccEntry);
				}
			}

			/*
			 * deal with the map entries
			 * --> just remove elem from each
			 */
			mAfCcPars.removeRangeElement(elem);
			mArgCcPars.removeRangeElement(elem);

			for (final Entry<ELEM, HashRelation<ELEM, ELEM>> en : mCcChildren.entrySet()) {
				assert !en.getKey().equals(elem) : "removed it in step before, right?";

				en.getValue().removeDomainElement(elem);
				en.getValue().removeRangeElement(elem);
			}
		}

		HashRelation<ELEM, ELEM> registerNewElement(final ELEM elem) {
			assert elem.isFunctionApplication() : "right?..";

			final ELEM afRep = mElementTVER.getRepresentative(elem.getAppliedFunction());
			final ELEM argRep = mElementTVER.getRepresentative(elem.getArgument());


			final HashRelation<ELEM, ELEM> equalitiesToPropagate = new HashRelation<>();
			final Set<ELEM> afCcPars = mAfCcPars.getImage(afRep);
			final Set<ELEM> candidates = afCcPars.stream()
					.filter(afccpar -> (hasElement(afccpar.getArgument()) &&
							getEqualityStatus(argRep, afccpar.getArgument()) == EqualityStatus.EQUAL))
					.collect(Collectors.toSet());
			candidates.forEach(c -> equalitiesToPropagate.addPair(elem, c));

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
			assert isRepresentative(rep);
			HashRelation<ELEM, ELEM> result = mCcChildren.get(rep);
			if (result == null) {
				result = new HashRelation<>();
				mCcChildren.put(rep, result);
			}
			return result;
		}

		private void addPropIfOneIsEqualOneIsUnconstrained(final ELEM af1, final ELEM arg1, final ELEM af2,
				final ELEM arg2,final HashRelation<ELEM, ELEM> result) {
			final EqualityStatus equalityStatusOfAppliedFunctions =
					getEqualityStatus(af1, af2);
			final EqualityStatus equalityStatusOfArguments =
					getEqualityStatus(arg1, arg2);

			if (equalityStatusOfAppliedFunctions == EqualityStatus.EQUAL
					&& equalityStatusOfArguments == EqualityStatus.UNKNOWN) {
				result.addPair(arg1, arg2);
			}

			if (equalityStatusOfAppliedFunctions == EqualityStatus.UNKNOWN
					&& equalityStatusOfArguments == EqualityStatus.EQUAL) {
				result.addPair(af1, af2);
			}
		}

		public Collection<ELEM> getAfCcPars(final ELEM elem) {
			assert isRepresentative(elem);
			return mAfCcPars.getImage(elem);
		}

		public Collection<ELEM> getArgCcPars(final ELEM elem) {
			assert isRepresentative(elem);
			return mArgCcPars.getImage(elem);
		}
	}
}
