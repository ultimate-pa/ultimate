package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public class CongruenceClosure<
		ELEM extends ICongruenceClosureElement<ELEM, FUNCTION>,
//		FUNCAPPELEM extends ICongruenceClosureFunctionApplication<ELEM, FUNCAPPELEM, FUNCTION>,
		FUNCTION> {
//		FUNCTION extends ICongruenceClosureFunction> {

	private final ThreeValuedEquivalenceRelation<ELEM> mElementTVER;

	private final ThreeValuedEquivalenceRelation<FUNCTION> mFunctionTVER;


//	/**
//	 * Contains for each function in the equivalence relation the representative of its equivalence class.
//	 */
//	private final Set<FUNCTION> mAllFunctionRepresentatives;


	private final NestedMap2<FUNCTION, ELEM, Set<ELEM>> mFunctionToRepresentativeToCcPars;

	private final NestedMap2<FUNCTION, ELEM, Set<List<ELEM>>> mFunctionToRepresentativeToCcChildren;

	private final HashRelation<FUNCTION, ELEM> mFunctionToFuncApps;

	public CongruenceClosure() {
		mElementTVER = new ThreeValuedEquivalenceRelation<>();
		mFunctionTVER = new ThreeValuedEquivalenceRelation<>();
		mFunctionToRepresentativeToCcPars = new NestedMap2<>();
		mFunctionToRepresentativeToCcChildren = new NestedMap2<>();
		mFunctionToFuncApps = new HashRelation<>();
//		mAllFunctionRepresentatives = new HashSet<>();
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

		/*
		 *  --> update mAllFunctionRepresentatives
		 */
//		if (newRep == f1OldRep) {
//			mFunctionToRepresentativeToCcPars.get(f2OldRep)
//			mFunctionToRepresentativeToCcPars.removeK1(f2OldRep);
//		} else {
//			assert newRep == f2OldRep;
//		}

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
//		for (final FUNCTION funcRep : mFunctionTVER.getAllRepresentatives()) {
		for (final Set<FUNCTION> eqc : mFunctionTVER.getAllEquivalenceClasses()) {
			for (final Pair<FUNCTION, FUNCTION> pair : getPairsFromSet(eqc, true, true)) {
				final Set<ELEM> e1CcPars = mFunctionToRepresentativeToCcPars.get(pair.getFirst(), e1OldRep);
				final Set<ELEM> e2CcPars = mFunctionToRepresentativeToCcPars.get(pair.getSecond(), e2OldRep);

				if (e1CcPars == null || e2CcPars == null) {
					// nothing to do
					continue;
				}

				// insert forward congruences
				for (final ELEM ccpar1 : e1CcPars) {
					for (final ELEM ccpar2 : e2CcPars) {
						if (argumentsAreCongruent(ccpar1, ccpar2)) {
							reportEqualityRec(ccpar1, ccpar2);
						}
					}
				}
			}
		}



		// do backward congruence propagations
		for (final FUNCTION funcRep : mFunctionTVER.getAllRepresentatives()) {
			final Set<List<ELEM>> e1CcChildren = mFunctionToRepresentativeToCcChildren.get(funcRep, e1OldRep);
			final Set<List<ELEM>> e2CcChildren = mFunctionToRepresentativeToCcChildren.get(funcRep, e2OldRep);

			if (e1CcChildren == null || e2CcChildren == null) {
				// nothing to do
				continue;
			}

			// insert backward congruences
			for (final List<ELEM> ccpar1 : e1CcChildren) {
				for (final List<ELEM> ccpar2 : e2CcChildren) {
					// if all other arguments are equal, we can propagate a disequality
					// TODO
				}
			}
		}

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

	/**
	 *
	 * @param funcApp1 function application element
	 * @param funcApp2 function application element
	 * @return true iff each two argument elements at the same position in the argument list are equal according to the
	 * 			current state of mElemenTVER
	 */
	private boolean argumentsAreCongruent(final ELEM funcApp1, final ELEM funcApp2) {
		assert funcApp1.isFunctionApplication() && funcApp2.isFunctionApplication();
		assert mFunctionTVER.getEquality(funcApp1.getAppliedFunction(), funcApp2.getAppliedFunction()) == Equality.EQUAL;
		assert funcApp1.getArguments().size() == funcApp2.getArguments().size();

		for (int i = 0; i < funcApp1.getArguments().size(); i++) {
			if (mElementTVER.getEquality(funcApp1.getArguments().get(i), funcApp2.getArguments().get(i))
					!= Equality.EQUAL) {
				return false;
			}
		}

		return true;
	}

	private void removeFromCcChildren(final ELEM elem, final FUNCTION func) {
		if (mFunctionToRepresentativeToCcChildren.get(func) == null) {
			// no entry for func present --> do nothing
			return;
		}
		mFunctionToRepresentativeToCcChildren.remove(func, elem);
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

	/**
	 * mFunctionToRepresentativeToCcPars only speaks about representatives.
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

	private boolean addElement(final ELEM elem) {
		final boolean newlyAdded = mElementTVER.getRepresentative(elem) == null;
		mElementTVER.addElement(elem);
		if (newlyAdded) {
//			for (final ELEM par : elem.getParents()) {
//				addToCcPar(elem, par);
//			}
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

	public FUNCTION getRepresentativeAndAddFunctionIfNeeded(final FUNCTION func) {
		return mFunctionTVER.getRepresentativeAndAddElementIfNeeded(func);
	}


	public ELEM getRepresentativeAndAddElementIfNeeded(final ELEM elem) {
		addElement(elem);
		return mElementTVER.getRepresentative(elem);
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

	public FUNCTION getRepresentativeFunction(final FUNCTION appliedFunction) {
		return mFunctionTVER.getRepresentative(appliedFunction);
	}

	public ELEM getRepresentative(final ELEM elem) {
		return mElementTVER.getRepresentative(elem);
	}

	public void reportDisequality(final ELEM e1, final ELEM e2) {

		mElementTVER.reportNotEquals(e1, e2);

		doBackwardCongruencePropagations(e1, e2);

		assert sanityCheck();

	}

	/**
	 * Assumes that a disequality between the given elements has just been introduced.
	 * Does the propagations that follow from that disequality and the function congruence axiom.
	 *
	 * @param e1
	 * @param e2
	 */
	private void doBackwardCongruencePropagations(final ELEM e1, final ELEM e2) {
		for (final FUNCTION func : mFunctionTVER.getAllRepresentatives()) {
			final Set<List<ELEM>> e1CcChildren = getCcChildren(func, e1);
			final Set<List<ELEM>> e2CcChildren = getCcChildren(func, e2);

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
			if (mElementTVER.getEquality(ccChildList1.get(i), ccChildList2.get(i)) == Equality.UNKNOWN) {
				if (result == -1) {
					result = i;
				} else {
					// we have more than 1 unknown position
					return -1;
				}
			} else if (mElementTVER.getEquality(ccChildList1.get(i), ccChildList2.get(i)) == Equality.NOT_EQUAL) {
				return -1;
			}
		}
		return result;
	}

	public void removeFunction(final FUNCTION f1) {
		mFunctionTVER.removeElement(f1);
	}

	public void removeElement(final ELEM e1) {
		mElementTVER.removeElement(e1);
	}

	public Equality getEqualityStatus(final ELEM elem1, final ELEM elem2) {
		return mElementTVER.getEquality(elem1, elem2);
	}

	public Equality getEqualityStatus(final FUNCTION elem1, final FUNCTION elem2) {
		return mFunctionTVER.getEquality(elem1, elem2);
	}

	public boolean containsContradiction() {
		return mElementTVER.containsContradiction() || mFunctionTVER.containsContradiction();
	}

	/**
	 *
	 * @return
	 */
	private boolean sanityCheck() {
		// the first, second and third field of mRepresentativeToFunctionToCcPars must only contain representatives
		// wrt. the underlying UnionFind
		for (final Triple<FUNCTION, ELEM, Set<ELEM>> repFuncCcPars : mFunctionToRepresentativeToCcPars.entrySet()) {
//			if (!mFunctionTVER.isRepresentative(repFuncCcPars.getFirst())) {
//				return false;
//			}
			if (!mElementTVER.isRepresentative(repFuncCcPars.getSecond())) {
				return false;
			}
		}

		for (final Triple<FUNCTION, ELEM, Set<List<ELEM>>> repFuncCcChildren
				: mFunctionToRepresentativeToCcChildren.entrySet()) {
//			if (!mFunctionTVER.isRepresentative(repFuncCcChildren.getFirst())) {
//				return false;
//			}
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

}
