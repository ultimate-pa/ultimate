package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.util.SetOperations;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ELEM>
 * @param <FUNCTION>
 */
public class CongruenceClosure<ELEM extends ICongruenceClosureElement<ELEM, FUNCTION>, FUNCTION> {

	private final ThreeValuedEquivalenceRelation<ELEM> mElementTVER;
	private final ThreeValuedEquivalenceRelation<FUNCTION> mFunctionTVER;

	private final NestedMap2<FUNCTION, ELEM, Set<ELEM>> mFunctionToRepresentativeToCcPars;
	private final NestedMap2<FUNCTION, ELEM, Set<List<ELEM>>> mFunctionToRepresentativeToCcChildren;
	private final HashRelation<FUNCTION, ELEM> mFunctionToFuncApps;
	private boolean mIsInconsistent;

	/**
	 * Constructs CongruenceClosure instance without any equalities or disequalities.
	 */
	public CongruenceClosure() {
		mElementTVER = new ThreeValuedEquivalenceRelation<>();
		mFunctionTVER = new ThreeValuedEquivalenceRelation<>();
		mFunctionToRepresentativeToCcPars = new NestedMap2<>();
		mFunctionToRepresentativeToCcChildren = new NestedMap2<>();
		mFunctionToFuncApps = new HashRelation<>();
		mIsInconsistent = false;
	}

	/**
	 * Constructs CongruenceClosure instance that is in an inconsistent state from the beginning.
	 *
	 * @param isInconsistent
	 */
	public CongruenceClosure(final boolean isInconsistent) {
		if (!isInconsistent) {
			throw new AssertionError("use other constructor");
		}
		mIsInconsistent = true;

		mElementTVER = null;
		mFunctionTVER = null;
		mFunctionToRepresentativeToCcPars = null;
		mFunctionToRepresentativeToCcChildren = null;
		mFunctionToFuncApps = null;
	}

	public CongruenceClosure(final UnionFind<ELEM> newElemPartition,
			final UnionFind<FUNCTION> newFunctionPartition,
			final HashRelation<ELEM, ELEM> newElemDisequalities,
			final HashRelation<FUNCTION, FUNCTION> newFunctionDisequalities) {
		mElementTVER = new ThreeValuedEquivalenceRelation<>(newElemPartition, newElemDisequalities);
		mFunctionTVER = new ThreeValuedEquivalenceRelation<>(newFunctionPartition, newFunctionDisequalities);
		mFunctionToRepresentativeToCcPars = new NestedMap2<>();
		mFunctionToRepresentativeToCcChildren = new NestedMap2<>();
		mFunctionToFuncApps = new HashRelation<>();
		assert !mElementTVER.isInconsistent() && !mFunctionTVER.isInconsistent();
		mIsInconsistent = false;

		// initialize the helper mappings according to mElementTVER
		for (final ELEM elem : mElementTVER.getAllElements()) {
			registerNewElement(elem);
		}
	}

	public void reportFunctionEquality(final FUNCTION f1, final FUNCTION f2) {
		final FUNCTION f1OldRep = getRepresentativeAndAddFunctionIfNeeded(f1);
		final FUNCTION f2OldRep = getRepresentativeAndAddFunctionIfNeeded(f2);

		if (f1OldRep == f2OldRep) {
			// already equal --> nothing to do
			return;
		}

		mFunctionTVER.reportEquality(f1, f2);

		/*
		 * congruence propagations:
		 *  if we are adding f = g
		 *  then we can propagate f(x) = g(x) for all nodes of that form we know.
		 *
		 *  uses optimization: don't iterate over all funcApps but only over representatives
		 *  (would it make sense that mFunctionToFuncApps only holds representatives??..)
		 */
		for (final ELEM funcApp1 : mFunctionToFuncApps.getImage(f1)
				.stream().map(fa -> mElementTVER.getRepresentative(fa)).collect(Collectors.toSet())) {
			for (final ELEM funcApp2 : mFunctionToFuncApps.getImage(f2)
					.stream().map(fa -> mElementTVER.getRepresentative(fa)).collect(Collectors.toSet())) {
				if (argumentsAreCongruent(funcApp1, funcApp2)) {
					reportEquality(funcApp1, funcApp2);
				}
			}
		}
		updateInconsistencyStatus();
	}

	public void reportFunctionDisequality(final FUNCTION f1, final FUNCTION f2) {
		mFunctionTVER.reportDisequality(f1, f2);
		updateInconsistencyStatus();
	}

	public void reportEquality(final ELEM e1, final ELEM e2) {
		if (mIsInconsistent) {
			throw new IllegalStateException();
		}

		boolean freshElem = false;
		freshElem |= addElement(e1);
		freshElem |= addElement(e2);

		if (!freshElem && getEqualityStatus(e1, e2) == EqualityStatus.EQUAL) {
			// nothing to do
			return;
		}
		if (!freshElem && getEqualityStatus(e1, e2) == EqualityStatus.NOT_EQUAL) {
			mIsInconsistent = true;
			return;
		}

		reportEqualityRec(e1, e2);
		updateInconsistencyStatus();
		assert sanityCheck();
	}

	public void reportDisequality(final ELEM e1, final ELEM e2) {
		if (mIsInconsistent) {
			throw new IllegalStateException();
		}

		boolean freshElem = false;
		freshElem |= addElement(e1);
		freshElem |= addElement(e2);

		if (!freshElem && getEqualityStatus(e1, e2) == EqualityStatus.NOT_EQUAL) {
			// nothing to do
			return;
		}
		if (!freshElem && getEqualityStatus(e1, e2) == EqualityStatus.EQUAL) {
			mIsInconsistent = true;
			return;
		}

		reportDisequalityRec(e1, e2);
		updateInconsistencyStatus();
		assert sanityCheck();
	}

	private void reportDisequalityRec(final ELEM e1, final ELEM e2) {
		mElementTVER.reportDisequality(e1, e2);
		if (mElementTVER.isInconsistent()) {
			return;
		}
		doBackwardCongruencePropagations(e1, e2);
	}

	private void reportEqualityRec(final ELEM e1, final ELEM e2) {

		final ELEM e1OldRep = getRepresentativeAndAddElementIfNeeded(e1);
		final ELEM e2OldRep = getRepresentativeAndAddElementIfNeeded(e2);

		if (e1OldRep == e2OldRep) {
			// already equal --> nothing to do
			return;
		}

		mElementTVER.reportEquality(e1, e2);

		final ELEM newRep = mElementTVER.getRepresentative(e1);

		// do forward congruence propagations
		for (final Set<FUNCTION> eqc : mFunctionTVER.getAllEquivalenceClasses()) {
			for (final Pair<FUNCTION, FUNCTION> pair : getPairsFromCollection(eqc, true, true)) {
				final Set<ELEM> e1CcPars = mFunctionToRepresentativeToCcPars.get(pair.getFirst(), e1OldRep);
				final Set<ELEM> e2CcPars = mFunctionToRepresentativeToCcPars.get(pair.getSecond(), e2OldRep);

				if (e1CcPars == null || e2CcPars == null) {
					// nothing to do
					continue;
				}

				for (final ELEM ccpar1 : e1CcPars) {
					for (final ELEM ccpar2 : e2CcPars) {
						// insert forward congruence
						if (argumentsAreCongruent(ccpar1, ccpar2)) {
							reportEqualityRec(ccpar1, ccpar2);
						}

						/*
						 * insert some backward congruences:
						 *
						 * say we knew before
						 * f(x1, x2) != g(y1, y2), and f = g
						 * now we are reporting x1 = y1
						 * --> then we need to propagate  x2 != y2 now.
						 */
						if (getEqualityStatus(ccpar1, ccpar2) == EqualityStatus.NOT_EQUAL) {
							final int onlyDifferentPos =
									getOnlyUnconstrainedPos(ccpar1.getArguments(), ccpar2.getArguments());
							if (onlyDifferentPos != -1) {
								reportDisequalityRec(ccpar1.getArguments().get(onlyDifferentPos),
										ccpar2.getArguments().get(onlyDifferentPos));
							}
						}
					}
				}
			}
		}

		/*
		 * do some more backward congruence propagations (see method documentation)
		 * we have two symmetric cases
		 */
		propagateDisequalities(e1OldRep, e2OldRep);
		propagateDisequalities(e2OldRep, e1OldRep);

		// update ccpar and ccchild sets
		for (final FUNCTION func : mFunctionTVER.getAllElements()) {
			final Set<ELEM> e1CcPars = mFunctionToRepresentativeToCcPars.get(func, e1OldRep);
			final Set<ELEM> e2CcPars = mFunctionToRepresentativeToCcPars.get(func, e2OldRep);

			final Set<List<ELEM>> e1CcChildren = mFunctionToRepresentativeToCcChildren.get(func, e1OldRep);
			final Set<List<ELEM>> e2CcChildren = mFunctionToRepresentativeToCcChildren.get(func, e2OldRep);

			// update CcPars -- add the elements in-place according to which element is the new representative
			final Set<ELEM> newCcPars = getCcPars(func, newRep);
			final Set<List<ELEM>> newCcChildren = getCcChildren(func, newRep);
			if (newRep == e1OldRep) {
				if (e2CcPars != null) {
					newCcPars.addAll(e2CcPars);
				}
				removeFromCcpars(e2OldRep, func);
				if (e2CcChildren != null) {
					newCcChildren.addAll(e2CcChildren);
				}
				removeFromCcChildren(e2OldRep, func);
			} else {
				assert newRep == e2OldRep;
				if (e1CcPars != null) {
					newCcPars.addAll(e1CcPars);
				}
				removeFromCcpars(e1OldRep, func);
				if (e1CcChildren != null) {
					newCcChildren.addAll(e1CcChildren);
				}
				removeFromCcChildren(e1OldRep, func);
			}
		}
	}

	/**
	 *
	 * @param elem
	 * @return true iff the element was not known to this CongruenceClosure before
	 */
	private boolean addElement(final ELEM elem) {
		final boolean newlyAdded = mElementTVER.addElement(elem);
		if (newlyAdded) {
			registerNewElement(elem);
		}
		return newlyAdded;
	}

	/**
	 * Updates the helper mappings for ccpars, ccchildren, and function applications. When a new element is added.
	 * @param elem
	 */
	private void registerNewElement(final ELEM elem) {
		if (elem.isFunctionApplication()) {
			mFunctionToFuncApps.addPair(elem.getAppliedFunction(), elem);

			getRepresentativeAndAddFunctionIfNeeded(elem.getAppliedFunction());

			addToCcChildren(elem, elem.getArguments());

			for (final ELEM arg : elem.getArguments()) {
				addElement(arg);
				addToCcPar(arg, elem);
			}

			/*
			 * As the new element is a function application, we might be able to infer equalities for it through
			 * congruence.
			 */
			for (final FUNCTION equivalentFunction : mFunctionTVER.getEquivalenceClass(elem.getAppliedFunction())) {
				Set<ELEM> candidateSet = null;

//				for (final ELEM arg : elem.getArguments()) {
				for (int i = 0; i < elem.getArguments().size(); i++) {
					final ELEM argRep = mElementTVER.getRepresentative(elem.getArguments().get(i));
//					final Set<ELEM> newCandidates = mFunctionToRepresentativeToCcPars.get(equivalentFunction, argRep);
					final Set<ELEM> newCandidates = getCcParsForArgumentPosition(equivalentFunction, argRep, i);
//					if (newCandidates == null) {
//						candidateSet = Collections.emptySet();
//						break;
//					}
					if (candidateSet == null) {
						candidateSet = new HashSet<>(newCandidates);
					} else {
						candidateSet.retainAll(newCandidates);
					}
				}

				for (final ELEM c : candidateSet) {
					if (c == elem) {
						continue;
					}
					reportEquality(elem, c);
				}
			}
		}
	}



	/**
	 * Retrieve CcPars of elem for function func that are parents for argument position i.
	 *
	 * @param equivalentFunction
	 * @param argRep
	 * @param i
	 * @return
	 */
	private Set<ELEM> getCcParsForArgumentPosition(final FUNCTION func, final ELEM elem, final int i) {
		/*
		 *  we take the ccpars from elem's equivalence class, but we filter, such that we only keep those ccpars who
		 *  have an element of the equivalence class at argument position i.
		 */
		final Set<ELEM> result = mFunctionToRepresentativeToCcPars.get(func, elem);
		if (result == null) {
			return Collections.emptySet();
		}
		return result.stream()
				.filter(par -> mElementTVER.getRepresentative(par.getArguments().get(i)).equals(elem))
				.collect(Collectors.toSet());
	}

	private void updateInconsistencyStatus() {
		mIsInconsistent |= mElementTVER.isInconsistent() || mFunctionTVER.isInconsistent();
	}

	/**
	 * Assumes that a disequality between the given elements has just been introduced.
	 * Does the propagations that follow from that disequality and the function congruence axiom.
	 *
	 * @param e1
	 * @param e2
	 */
	private void doBackwardCongruencePropagations(final ELEM e1, final ELEM e2) {
		for (final Set<FUNCTION> eqc : mFunctionTVER.getAllEquivalenceClasses()) {
			for (final Pair<FUNCTION, FUNCTION> pair : getPairsFromCollection(eqc, true, true)) {

				final Set<List<ELEM>> e1CcChildren = getCcChildren(pair.getFirst(), e1);
				final Set<List<ELEM>> e2CcChildren = getCcChildren(pair.getSecond(), e2);

				for (final List<ELEM> ccChildList1 : e1CcChildren) {
					for (final List<ELEM> ccChildList2 : e2CcChildren) {
						final int onlyUnconstrainedPos = getOnlyUnconstrainedPos(ccChildList1, ccChildList2);
						if (onlyUnconstrainedPos != -1) {
							reportDisequality(ccChildList1.get(onlyUnconstrainedPos),
									ccChildList2.get(onlyUnconstrainedPos));
						}
					}
				}
			}
		}
	}

	/**
	 * This method is a helper that, for two representatives of equivalence classes checks if, because of merging the
	 * two equivalence classes, any disequality propagations are possible.
	 *
	 * Example:
	 *  <li> preState:
	 *   (i = f(y)) , (j != f(x)), (i = j)
	 *  <li> we just added an equality between i and j (did the merge operation)
	 *  <li> one call of this method will be with (preState, i, f(x))
	 *  <li> we will get the output state:
	 *   (i = f(y)) , (j != f(x)), (i = j), (x != y)
	 *
	 * @param e1OldRep
	 * @param e2OldRep
	 */
	private void propagateDisequalities(final ELEM e1OldRep, final ELEM e2OldRep) {
		for (final ELEM repUnequalToE1 : mElementTVER.getRepresentativesUnequalTo(e1OldRep)) {
			for (final Set<FUNCTION> eqc : mFunctionTVER.getAllEquivalenceClasses()) {
				for (final Pair<FUNCTION, FUNCTION> pair : getPairsFromCollection(eqc, true, true)) {
					final Set<ELEM> funcApps1 =
							getFunctionApplicationsInSameEquivalenceClass(pair.getFirst(), repUnequalToE1);
					final Set<ELEM> funcApps2 =
							getFunctionApplicationsInSameEquivalenceClass(pair.getSecond(), e2OldRep);

					if (funcApps1 == null || funcApps2 == null) {
						// nothing to do
						continue;
					}

					for (final ELEM ccpar1 : funcApps1) {
						for (final ELEM ccpar2 : funcApps2) {
							final int onlyDifferentPos =
									getOnlyUnconstrainedPos(ccpar1.getArguments(), ccpar2.getArguments());
							if (onlyDifferentPos != -1) {
								reportDisequalityRec(ccpar1.getArguments().get(onlyDifferentPos),
										ccpar2.getArguments().get(onlyDifferentPos));
							}
						}
					}
				}
			}
		}
	}

	public FUNCTION getRepresentativeAndAddFunctionIfNeeded(final FUNCTION func) {
		return mFunctionTVER.getRepresentativeAndAddElementIfNeeded(func);
	}


	public ELEM getRepresentativeAndAddElementIfNeeded(final ELEM elem) {
		addElement(elem);
		return mElementTVER.getRepresentative(elem);
	}

	public FUNCTION getRepresentativeFunction(final FUNCTION appliedFunction) {
		return mFunctionTVER.getRepresentative(appliedFunction);
	}

	public ELEM getRepresentativeElement(final ELEM elem) {
		return mElementTVER.getRepresentative(elem);
	}

	public void removeFunction(final FUNCTION func) {
		// remove from the function equivalence relation
		mFunctionTVER.removeElement(func);

		// remove all elements that depend on the function
		for (final ELEM funcApp : mFunctionToFuncApps.getImage(func)) {
			removeElement(funcApp);
		}

		mFunctionToRepresentativeToCcPars.remove(func);
		mFunctionToRepresentativeToCcChildren.remove(func);
		mFunctionToFuncApps.removeDomainElement(func);
	}

	public void removeElement(final ELEM elem) {
		if (mElementTVER.isRepresentative(elem)) {
			for (final FUNCTION func : mFunctionTVER.getAllElements()) {
				mFunctionToRepresentativeToCcPars.get(func).remove(elem);
				mFunctionToRepresentativeToCcChildren.get(func).remove(elem);
			}
		}
		mFunctionToFuncApps.removeRangeElement(elem);

		mElementTVER.removeElement(elem);

		for (final ELEM parent : elem.getParents()) {
			removeElement(parent);
		}

	}

	public CongruenceClosure<ELEM, FUNCTION> join(final CongruenceClosure<ELEM, FUNCTION> other) {
		assert haveSameElements(this.mElementTVER, other.mElementTVER);
		assert haveSameElements(this.mFunctionTVER, other.mFunctionTVER);
		return joinOrMeet(other, true);
	}

	public CongruenceClosure<ELEM, FUNCTION> meet(final CongruenceClosure<ELEM, FUNCTION> other) {
		assert haveSameElements(this.mElementTVER, other.mElementTVER);
		assert haveSameElements(this.mFunctionTVER, other.mFunctionTVER);
		return joinOrMeet(other, false);
	}

	/**
	 *
	 * @param other
	 * @return true iff this CongruenceClosure is equally or more constraining, than the other given CongruenceClosure
	 */
	public boolean isStrongerThan(final CongruenceClosure<ELEM, FUNCTION> other) {
		/*
		 * We check for each equivalence representative in "other" if its equivalence class is a subset of the
		 * equivalence class of the representative in "this".
		 *
		 * (going through the representatives in "this" would be unsound because we might not see all relevant
		 *  equivalence classes in "other")
		 */
		if (!isPartitionStronger(this.mElementTVER, other.mElementTVER)) {
			return false;
		}
		if (!isPartitionStronger(this.mFunctionTVER, other.mFunctionTVER)) {
			return false;
		}

		/*
		 * We check if each disequality that holds in "other" also holds in "this".
		 */
		if (!areDisequalitiesStrongerThan(this.mElementTVER, other.mElementTVER)) {
			return false;
		}
		if (!areDisequalitiesStrongerThan(this.mFunctionTVER, other.mFunctionTVER)) {
			return false;
		}
		return true;
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
	 * @return true if first is more constraining
	 */
	private static <E> boolean isPartitionStronger(final ThreeValuedEquivalenceRelation<E> first,
			final ThreeValuedEquivalenceRelation<E> second) {
		for (final E otherRep : second.getAllRepresentatives()) {
			final Set<E> eqInOther = second.getEquivalenceClass(otherRep);
			final Set<E> eqInThis = first.getEquivalenceClass(otherRep);
			if (!eqInThis.containsAll(eqInOther)) {
				return false;
			}
		}
		return true;
	}

	public EqualityStatus getEqualityStatus(final FUNCTION elem1, final FUNCTION elem2) {
		return mFunctionTVER.getEqualityStatus(elem1, elem2);
	}

	public EqualityStatus getEqualityStatus(final ELEM elem1, final ELEM elem2) {
		return mElementTVER.getEqualityStatus(elem1, elem2);
	}

	public boolean isInconsistent() {
		return mIsInconsistent;
	}

	/**
	 * @param other
	 * @param join true if this method should compute the Join, false if it should compute the Meet of "this" and
	 * 		"other".
	 * @return
	 */
	private CongruenceClosure<ELEM, FUNCTION> joinOrMeet(final CongruenceClosure<ELEM, FUNCTION> other,
			final boolean join) {
		final UnionFind<ELEM> newElemPartition = xJoinPartitionBlocks(this.mElementTVER, other.mElementTVER, join);
		final UnionFind<FUNCTION> newFunctionPartition = xJoinPartitionBlocks(this.mFunctionTVER,
				other.mFunctionTVER, join);

		// If we are computing the Meet, we may introduce a contradiction --> check for this here
		if (newElemPartition == null || newFunctionPartition == null) {
			assert !join;
			return new CongruenceClosure<>(true);
		}

		final HashRelation<ELEM, ELEM> newElemDisequalities = xJoinDisequalities(this.mElementTVER,
				other.mElementTVER, newElemPartition, join);
		final HashRelation<FUNCTION, FUNCTION> newFunctionDisequalities = xJoinDisequalities(this.mFunctionTVER,
				other.mFunctionTVER, newFunctionPartition, join);

		return new CongruenceClosure<>(newElemPartition, newFunctionPartition, newElemDisequalities,
				newFunctionDisequalities);
	}


	/**
	 * Conjoin or disjoin two disequality relations.
	 *
	 * @param tver1
	 * @param tver2
	 * @param newElemPartition
	 * @param conjoin conjoin or disjoin?
	 * @return
	 */
	private static <E> HashRelation<E, E> xJoinDisequalities(final ThreeValuedEquivalenceRelation<E> tver1,
			final ThreeValuedEquivalenceRelation<E> tver2, final UnionFind<E> newElemPartition, final boolean conjoin) {
		final HashRelation<E, E> result = new HashRelation<>();
		for (final Pair<E, E> pair : getPairsFromCollection(newElemPartition.getAllRepresentatives(),
				false, false)) {
			final boolean addDisequality;
			if (conjoin) {
				addDisequality = tver1.getEqualityStatus(pair.getFirst(), pair.getSecond()) == EqualityStatus.NOT_EQUAL
						&& tver2.getEqualityStatus(pair.getFirst(), pair.getSecond()) == EqualityStatus.NOT_EQUAL;
			} else {
				addDisequality = tver1.getEqualityStatus(pair.getFirst(), pair.getSecond()) == EqualityStatus.NOT_EQUAL
						|| tver2.getEqualityStatus(pair.getFirst(), pair.getSecond()) == EqualityStatus.NOT_EQUAL;
			}
			if (addDisequality) {
				result.addPair(pair.getFirst(), pair.getSecond());
			}
		}
		return result;
	}

	/**
	 * Conjoin (intersect) or disjoin (union) partition blocks from this and other according to the given flag
	 *
	 * @param tver1
	 * @param tver2
	 * @return .. null, if there is a contradiction to the disequalities in either tver
	 */
	private static <E> UnionFind<E> xJoinPartitionBlocks(final ThreeValuedEquivalenceRelation<E> tver1,
			final ThreeValuedEquivalenceRelation<E> tver2, final boolean conjoin) {
		final UnionFind<E> result = new UnionFind<>();
		for (final E rep : concatenateCollections(
				tver1.getAllRepresentatives(),
				tver2.getAllRepresentatives())) {
			final Set<E> thisEqc = tver1.getEquivalenceClass(rep);
			final Set<E> otherEqc = tver2.getEquivalenceClass(rep);
			if (conjoin) {
				result.addEquivalenceClass(SetOperations.intersect(thisEqc, otherEqc));
			} else {
				// disjoin/Meet case : we also check for contradictions here.
				if (tver1.isRepresentative(rep)) {
					final E tver2Rep = tver2.getRepresentative(rep);
					if (tver1.getEqualityStatus(rep, tver2Rep) == EqualityStatus.NOT_EQUAL
						|| tver2.getEqualityStatus(rep, tver2Rep) == EqualityStatus.NOT_EQUAL) {
							return null;
					}
				} else {
					assert tver2.isRepresentative(rep);
					final E tver1Rep = tver1.getRepresentative(rep);
					if (tver1.getEqualityStatus(rep, tver1Rep) == EqualityStatus.NOT_EQUAL
						|| tver2.getEqualityStatus(rep, tver1Rep) == EqualityStatus.NOT_EQUAL) {
							return null;
					}
				}
				result.addEquivalenceClass(SetOperations.union(thisEqc, otherEqc));
			}
		}
		return result;
	}

	/**
	 *
	 * @param funcApp1 function application element
	 * @param funcApp2 function application element
	 * @return true iff each two argument elements at the same position in the argument list are equal according to the
	 * 			current state of mElemenTVER
	 */
	private boolean argumentsAreCongruent(final ELEM funcApp1, final ELEM funcApp2) {
		assert funcApp1.isFunctionApplication() && funcApp2.isFunctionApplication();
		assert mFunctionTVER.getEqualityStatus(funcApp1.getAppliedFunction(), funcApp2.getAppliedFunction()) == EqualityStatus.EQUAL;
		assert funcApp1.getArguments().size() == funcApp2.getArguments().size();

		for (int i = 0; i < funcApp1.getArguments().size(); i++) {
			if (mElementTVER.getEqualityStatus(funcApp1.getArguments().get(i), funcApp2.getArguments().get(i))
					!= EqualityStatus.EQUAL) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Checks if all entries of the given lists are equal (at the matching list index) on all positions except for one.
	 * Returns that position if it exists, -1 otherwise.
	 *
	 * @param ccChild1
	 * @param ccChild2
	 * @return the only position in where the equality status between the entries of the lists is UNKOWN according to
	 * 		mElementTVER when all other positions have status EQUAL, -1 if no such position exists
	 */
	private int getOnlyUnconstrainedPos(final List<ELEM> ccChildList1, final List<ELEM> ccChildList2) {
		assert ccChildList1.size() == ccChildList2.size();
		int result = -1;
		for (int i = 0; i < ccChildList1.size(); i++) {
			if (mElementTVER.getEqualityStatus(ccChildList1.get(i), ccChildList2.get(i)) == EqualityStatus.UNKNOWN) {
				if (result == -1) {
					result = i;
				} else {
					// we have more than 1 unknown position
					return -1;
				}
			} else if (mElementTVER.getEqualityStatus(ccChildList1.get(i), ccChildList2.get(i)) == EqualityStatus.NOT_EQUAL) {
				return -1;
			}
		}
		return result;
	}

	private Set<ELEM> getFunctionApplicationsInSameEquivalenceClass(final FUNCTION func, final ELEM elem) {
		return mElementTVER.getEquivalenceClass(elem).stream()
				.filter(el -> el.isFunctionApplication() && el.getAppliedFunction() == func)
				.collect(Collectors.toSet());
	}

	/**
	 * Add the function application element funcApp to the CcPar set of elem class.
	 * (more precisely: do this for their equivalence representatives)
	 *
	 * @param elem
	 * @param funcApp
	 */
	private void addToCcPar(final ELEM elem, final ELEM funcApp) {
		final ELEM funcAppRep = getRepresentativeElement(funcApp);
//		final FUNCTION funcRep = getRepresentativeFunction(funcApp.getAppliedFunction());
		final FUNCTION func = funcApp.getAppliedFunction();
		final ELEM elemRep = getRepresentativeElement(elem);

		Set<ELEM> ccpars = mFunctionToRepresentativeToCcPars.get(func, elemRep);
		if (ccpars == null) {
			ccpars = new HashSet<>();
			mFunctionToRepresentativeToCcPars.put(func, elemRep, ccpars);
		}
		ccpars.add(funcAppRep);
	}

	private void addToCcChildren(final ELEM elem, final List<ELEM> arguments) {
		assert elem.isFunctionApplication();
		final FUNCTION funcRep = getRepresentativeFunction(elem.getAppliedFunction());
		final ELEM elemRep = getRepresentativeElement(elem);

		Set<List<ELEM>> ccChildrenSet = mFunctionToRepresentativeToCcChildren.get(funcRep, elemRep);

		if (ccChildrenSet == null) {
			ccChildrenSet = new HashSet<>();
			mFunctionToRepresentativeToCcChildren.put(funcRep, elemRep, ccChildrenSet);
		}
		ccChildrenSet.add(arguments);
	}

	/**
	 * mFunctionToRepresentativeToCcPars only speaks about representatives (in the second entry).
	 * This is called when the given ELEM is no more a representative an thus its whole
	 * entry in the nested map can be removed.
	 *
	 * @param e2OldRep
	 * @param func
	 */
	private void removeFromCcpars(final ELEM e2OldRep, final FUNCTION func) {
		if (mFunctionToRepresentativeToCcPars.get(func) == null) {
			// no entry for func present --> do nothing
			return;
		}
		mFunctionToRepresentativeToCcPars.remove(func, e2OldRep);
	}

	private void removeFromCcChildren(final ELEM elem, final FUNCTION func) {
		if (mFunctionToRepresentativeToCcChildren.get(func) == null) {
			// no entry for func present --> do nothing
			return;
		}
		mFunctionToRepresentativeToCcChildren.remove(func, elem);
	}

	/**
	 * Retrieves the ccpar map for the given function and element (both must be representatives)
	 * Creates one if there is none..
	 * @param funcRep
	 * @param newRep
	 * @return
	 */
	private Set<ELEM> getCcPars(final FUNCTION funcRep, final ELEM newRep) {
		Set<ELEM> res = mFunctionToRepresentativeToCcPars.get(funcRep, newRep);
		if (res == null) {
			res = new HashSet<>();
			mFunctionToRepresentativeToCcPars.put(funcRep, newRep, res);
		}
		return res;
	}

	private Set<List<ELEM>> getCcChildren(final FUNCTION funcRep, final ELEM newRep) {
		assert mElementTVER.isRepresentative(newRep);
		Set<List<ELEM>> res = mFunctionToRepresentativeToCcChildren.get(funcRep, newRep);
		if (res == null) {
			res = new HashSet<>();
			mFunctionToRepresentativeToCcChildren.put(funcRep, newRep, res);
		}
		return res;
	}

	/**
	 * Check for some class invariants.
	 *
	 * @return
	 */
	private boolean sanityCheck() {
		// the first, second and third field of mRepresentativeToFunctionToCcPars must only contain representatives
		// wrt. the underlying UnionFind
		for (final Triple<FUNCTION, ELEM, Set<ELEM>> repFuncCcPars : mFunctionToRepresentativeToCcPars.entrySet()) {
			if (!mElementTVER.isRepresentative(repFuncCcPars.getSecond())) {
				return false;
			}
		}

		for (final Triple<FUNCTION, ELEM, Set<List<ELEM>>> repFuncCcChildren
				: mFunctionToRepresentativeToCcChildren.entrySet()) {
			if (!mElementTVER.isRepresentative(repFuncCcChildren.getSecond())) {
				return false;
			}
		}

		if (!mIsInconsistent) {
			if (mElementTVER.isInconsistent()) {
				return false;
			}
			if (mFunctionTVER.isInconsistent()) {
				return false;
			}
			if (mElementTVER == null) {
				return false;
			}
		}

		return true;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();

		sb.append("Element equivalences:");
		sb.append(mElementTVER);
		sb.append("\n");

		sb.append("Function equivalences:");
		sb.append(mFunctionTVER);

		return sb.toString();
	}

	static <E> boolean haveSameElements(final ThreeValuedEquivalenceRelation<E> tver1,
			final ThreeValuedEquivalenceRelation<E> tver2) {
		return tver1.getAllElements().equals(tver2.getAllElements());
	}

	static <E> Collection<Pair<E, E>> getPairsFromCollection(final Collection<E> set, final boolean returnReflexivePairs,
			final boolean returnSymmetricPairs) {
		final Collection<Pair<E, E>> result = new ArrayList<>();

		final Iterator<E> it1 = set.iterator();
		for (int i = 0; i < set.size(); i++) {
			final E el1 = it1.next();
			final Iterator<E> it2 = set.iterator();
			for (int j = 0; (!returnSymmetricPairs && j <= i) || (returnSymmetricPairs && j < set.size()); j++) {
				final E el2 = it2.next();
				if (!returnReflexivePairs && j == i) {
					continue;
				}
				result.add(new Pair<E, E>(el1, el2));
			}
		}
		return result;
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

}
