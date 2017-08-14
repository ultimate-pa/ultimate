package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.ArrayList;
import java.util.Collection;
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

	public CongruenceClosure() {
		mElementTVER = new ThreeValuedEquivalenceRelation<>();
		mFunctionTVER = new ThreeValuedEquivalenceRelation<>();
		mFunctionToRepresentativeToCcPars = new NestedMap2<>();
		mFunctionToRepresentativeToCcChildren = new NestedMap2<>();
		mFunctionToFuncApps = new HashRelation<>();
	}

	public CongruenceClosure(final UnionFind<ELEM> newElemPartition,
			final UnionFind<FUNCTION> newFunctionPartition,
			final HashRelation<ELEM, ELEM> newElemDisequalities,
			final HashRelation<FUNCTION, FUNCTION> newFunctionDisequalities) {
		mElementTVER = new ThreeValuedEquivalenceRelation<>(newElemPartition, newElemDisequalities);
		mFunctionTVER = new ThreeValuedEquivalenceRelation<>(newFunctionPartition, newFunctionDisequalities);

		final Triple<NestedMap2<FUNCTION, ELEM, Set<ELEM>>,
			NestedMap2<FUNCTION, ELEM, Set<List<ELEM>>>,
			HashRelation<FUNCTION, ELEM>> init = computeMappingsFromTVERs(mElementTVER, mFunctionTVER);

		mFunctionToRepresentativeToCcPars = init.getFirst();
		mFunctionToRepresentativeToCcChildren = init.getSecond();
		mFunctionToFuncApps = init.getThird();

	}

	private Triple<NestedMap2<FUNCTION, ELEM, Set<ELEM>>,
				NestedMap2<FUNCTION, ELEM, Set<List<ELEM>>>,
				HashRelation<FUNCTION, ELEM>> computeMappingsFromTVERs(
						final ThreeValuedEquivalenceRelation<ELEM> elementTVER,
						final ThreeValuedEquivalenceRelation<FUNCTION> functionTVER) {
		// TODO Auto-generated method stub
		assert false;
		return null;
	}

	public void reportFunctionEquality(final FUNCTION f1, final FUNCTION f2) {
		final FUNCTION f1OldRep = getRepresentativeAndAddFunctionIfNeeded(f1);
		final FUNCTION f2OldRep = getRepresentativeAndAddFunctionIfNeeded(f2);

		if (f1OldRep == f2OldRep) {
			// already equal --> nothing to do
			return;
		}

		mFunctionTVER.reportEquality(f1, f2);

		final FUNCTION newRep = mFunctionTVER.getRepresentative(f1);

		for (final ELEM funcApp1 : mFunctionToFuncApps.getImage(f1)) {
			for (final ELEM funcApp2 : mFunctionToFuncApps.getImage(f2)) {
				if (argumentsAreCongruent(funcApp1, funcApp2)) {
					reportEquality(funcApp1, funcApp2);
				}
			}
		}
	}
	public void reportFunctionDisequality(final FUNCTION f1, final FUNCTION f2) {
		mFunctionTVER.reportDisequality(f1, f2);
	}

	public void reportEquality(final ELEM e1, final ELEM e2) {
		reportEqualityRec(e1, e2);
		assert sanityCheck();
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
			for (final Pair<FUNCTION, FUNCTION> pair : getPairsFromSet(eqc, true, true)) {
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

	private boolean addElement(final ELEM elem) {
		final boolean newlyAdded = mElementTVER.getRepresentative(elem) == null;
		mElementTVER.addElement(elem);
		if (newlyAdded) {
			if (elem.isFunctionApplication()) {
				mFunctionToFuncApps.addPair(elem.getAppliedFunction(), elem);

				getRepresentativeAndAddFunctionIfNeeded(elem.getAppliedFunction());

				addToCcChildren(elem, elem.getArguments());

				for (final ELEM arg : elem.getArguments()) {
					addToCcPar(arg, elem);
				}
			}
		}
		return newlyAdded;
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

	public ELEM getRepresentative(final ELEM elem) {
		return mElementTVER.getRepresentative(elem);
	}

	public void reportDisequality(final ELEM e1, final ELEM e2) {
		reportDisequalityRec(e1, e2);
		assert sanityCheck();
	}

	public void reportDisequalityRec(final ELEM e1, final ELEM e2) {

		mElementTVER.reportDisequality(e1, e2);

		doBackwardCongruencePropagations(e1, e2);
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
			for (final Pair<FUNCTION, FUNCTION> pair : getPairsFromSet(eqc, true, true)) {

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
				for (final Pair<FUNCTION, FUNCTION> pair : getPairsFromSet(eqc, true, true)) {
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

	public EqualityStatus getEqualityStatus(final ELEM elem1, final ELEM elem2) {
		return mElementTVER.getEqualityStatus(elem1, elem2);
	}

	public EqualityStatus getEqualityStatus(final FUNCTION elem1, final FUNCTION elem2) {
		return mFunctionTVER.getEqualityStatus(elem1, elem2);
	}

	public boolean containsContradiction() {
		return mElementTVER.isInconsistent() || mFunctionTVER.isInconsistent();
	}

	public CongruenceClosure<ELEM, FUNCTION> join(final CongruenceClosure<ELEM, FUNCTION> other) {
		final UnionFind<ELEM> newElemPartition = intersectPartitionBlocks(this.mElementTVER, other.mElementTVER);
		final UnionFind<FUNCTION> newFunctionPartition = intersectPartitionBlocks(this.mFunctionTVER, other.mFunctionTVER);

		// TODO: initialize correctly
		assert false;
		final HashRelation<ELEM, ELEM> newElemDisequalities = null;
		final HashRelation<FUNCTION, FUNCTION> newFunctionDisequalities = null;

		return new CongruenceClosure<>(newElemPartition, newFunctionPartition, newElemDisequalities,
				newFunctionDisequalities);
	}

	private static <E> UnionFind<E> intersectPartitionBlocks(final ThreeValuedEquivalenceRelation<E> tver1,
			final ThreeValuedEquivalenceRelation<E> tver2) {
//		final Set<Set<E>> newElemPartition = new HashSet<>();
		final UnionFind<E> result = new UnionFind<>();
		for (final E thisRep : concatenateCollections(
				tver1.getAllRepresentatives(),
				tver2.getAllRepresentatives())) {
			final Set<E> thisEqc = tver1.getEquivalenceClass(thisRep);
			final Set<E> otherEqc = tver2.getEquivalenceClass(thisRep);
//			newElemPartition.add(SetOperations.intersect(thisEqc, otherEqc));
			result.addEquivalenceClass(SetOperations.intersect(thisEqc, otherEqc));
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
		final ELEM funcAppRep = getRepresentative(funcApp);
		final FUNCTION funcRep = getRepresentativeFunction(funcApp.getAppliedFunction());
		final ELEM elemRep = getRepresentative(elem);

		Set<ELEM> ccpars = mFunctionToRepresentativeToCcPars.get(funcRep, elemRep);
		if (ccpars == null) {
			ccpars = new HashSet<>();
			mFunctionToRepresentativeToCcPars.put(funcRep, elemRep, ccpars);
		}
		ccpars.add(funcAppRep);
	}

	private void addToCcChildren(final ELEM elem, final List<ELEM> arguments) {
		assert elem.isFunctionApplication();
		final FUNCTION funcRep = getRepresentativeFunction(elem.getAppliedFunction());
		final ELEM elemRep = getRepresentative(elem);

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

	static <E> Collection<Pair<E, E>> getPairsFromSet(final Set<E> set, final boolean returnReflexivePairs,
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
