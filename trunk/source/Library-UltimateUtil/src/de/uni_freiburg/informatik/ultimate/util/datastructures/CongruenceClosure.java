package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
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

	/**
	 * conventions:
	 * <li> function f (first index) is not a representative, every function known to mFunctionTVER can have an entry
	 * 	here
	 * <li> representative r (second index) is a representative of an equivalence class in mElemenTVER
	 * <li> the result set, ccpars, contains nodes that are an f-parent of a node in r's equivalence class.
	 * <p>
	 * usage of this map: reportEqualityRec, together with argumentsAreCongruent
	 */
	protected final NestedMap2<ELEM, ELEM, Set<ELEM>> mFunctionToRepresentativeToCcPars;
	protected final NestedMap2<ELEM, ELEM, Set<List<ELEM>>> mFunctionToRepresentativeToCcChildren;
	protected final HashRelation<ELEM, ELEM> mFunctionToFuncApps;

	/**
	 * stores all known parents for an element -- used for remove method to also remove dependent elements
	 * (might be used for other dependencies, too..
	 */
	protected final HashRelation<ELEM, ELEM> mElementToParents;

	private boolean mIsInconsistent;

	private final Set<ELEM> mAllFunctions;


	/**
	 * Constructs CongruenceClosure instance without any equalities or
	 * disequalities.
	 */
	public CongruenceClosure() {
		mElementTVER = new ThreeValuedEquivalenceRelation<>();
		mFunctionToRepresentativeToCcPars = new NestedMap2<>();
		mFunctionToRepresentativeToCcChildren = new NestedMap2<>();
		mFunctionToFuncApps = new HashRelation<>();
		mElementToParents = new HashRelation<>();
		mAllFunctions = new HashSet<>();
		mIsInconsistent = false;
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
		mIsInconsistent = true;

		mElementTVER = null;
		mFunctionToRepresentativeToCcPars = null;
		mFunctionToRepresentativeToCcChildren = null;
		mFunctionToFuncApps = null;
		mElementToParents = null;
		mAllFunctions = null;
	}

	public CongruenceClosure(final ThreeValuedEquivalenceRelation<ELEM> newElemPartition) {
		mElementTVER = newElemPartition;
		mFunctionToRepresentativeToCcPars = new NestedMap2<>();
		mFunctionToRepresentativeToCcChildren = new NestedMap2<>();
		mFunctionToFuncApps = new HashRelation<>();
		mElementToParents = new HashRelation<>();
		assert !mElementTVER.isInconsistent();
		mIsInconsistent = false;
		mAllFunctions = new HashSet<>();

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
		mFunctionToRepresentativeToCcPars = new NestedMap2<>(original.mFunctionToRepresentativeToCcPars);
		mFunctionToRepresentativeToCcChildren = new NestedMap2<>(original.mFunctionToRepresentativeToCcChildren);
		mFunctionToFuncApps = new HashRelation<>(original.mFunctionToFuncApps);
		mElementToParents = new HashRelation<>(original.mElementToParents);
		mAllFunctions = new HashSet<>(original.mAllFunctions);
		assert !original.mIsInconsistent;
		mIsInconsistent = false;
		assert sanityCheck();
	}

//	/**
//	 *
//	 * @param func1
//	 * @param func2
//	 * @return true iff the state of this CongruenceClosure instance has changed through this method call
//	 */
//	private boolean reportFunctionEquality(final ELEM func1, final ELEM func2) {
//		boolean freshFunc = false;
//		freshFunc |= addFunction(func1);
//		freshFunc |= addFunction(func2);
//
//		if (getEqualityStatus(func1, func2) == EqualityStatus.EQUAL) {
//			// already equal --> nothing to do
//			assert !freshFunc;
//			return false;
//		}
//
////		mFunctionTVER.reportEquality(func1, func2);
//		mElementTVER.reportEquality(func1, func2);
//		updateInconsistencyStatus();
//		if (isInconsistent()) {
//			// no need to propagate anything if this is already inconsistent
//			return true;
//		}
//
//		/*
//		 * congruence propagations: if we are adding f = g then we can propagate f(x) =
//		 * g(x) for all nodes of that form we know.
//		 *
//		 */
//		for (final ELEM funcApp1 : mFunctionToFuncApps.getImage(func1)) {
//			for (final ELEM funcApp2 : mFunctionToFuncApps.getImage(func2)) {
//				if (funcApp1 == funcApp2) {
//					continue;
//				}
//				if (argumentsAreCongruent(funcApp1, funcApp2)) {
//					reportEquality(funcApp1, funcApp2);
//				}
//			}
//		}
//		updateInconsistencyStatus();
//		assert sanityCheck();
//		return true;
//	}

//	private boolean addFunction(final ELEM func) {
////		final boolean newlyAdded = mFunctionTVER.addElement(func);
//		final boolean newlyAdded = mElementTVER.addElement(func);
//		if (!newlyAdded) {
//			return false;
//		}
//		registerNewFunction(func);
//		return true;
//	}
//
//	private void registerNewFunction(final ELEM func) {
//		mAllFunctions.add(func);
//	}

//	/**
//	 *
//	 * @param func1
//	 * @param func2
//	 * @return
//	 */
//	public boolean reportFunctionDisequality(final ELEM func1, final ELEM func2) {
//		if (getEqualityStatus(func1, func2) == EqualityStatus.NOT_EQUAL) {
//			return false;
//		}
////		mFunctionTVER.reportDisequality(func1, func2);
//		mElementTVER.reportDisequality(func1, func2);
//		updateInconsistencyStatus();
//		assert sanityCheck();
//		return true;
//	}

	public boolean reportEquality(final ELEM elem1, final ELEM elem2) {
		if (mIsInconsistent) {
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
			mIsInconsistent = true;
			return true;
		}

		reportEqualityRec(elem1, elem2);
		updateInconsistencyStatus();
		assert sanityCheck();
		return true;
	}

	public boolean reportDisequality(final ELEM elem1, final ELEM elem2) {
		if (mIsInconsistent) {
			throw new IllegalStateException();
		}

		boolean freshElem = false;
		freshElem |= addElement(elem1);
		freshElem |= addElement(elem2);

		if (!freshElem && getEqualityStatus(elem1, elem2) == EqualityStatus.NOT_EQUAL) {
			// nothing to do
			return false;
		}

		reportDisequalityRec(elem1, elem2, mFunctionToRepresentativeToCcChildren);
		assert sanityCheck();
		return true;
	}

	protected boolean reportDisequalityRec(final ELEM elem1, final ELEM elem2,
			final NestedMap2<ELEM, ELEM, Set<List<ELEM>>> oldCcChild) {
		if (mElementTVER.getEqualityStatus(elem1, elem2) == EqualityStatus.NOT_EQUAL) {
			return false;
		}
		mElementTVER.reportDisequality(elem1, elem2);
		if (mElementTVER.isInconsistent()) {
			updateInconsistencyStatus();
			return true;
		}
		doBackwardCongruencePropagations(elem1, elem2, oldCcChild);
		return true;
	}

	protected boolean reportEqualityRec(final ELEM elem1, final ELEM elem2) {

		final ELEM e1OldRep = getRepresentativeAndAddElementIfNeeded(elem1);
		final ELEM e2OldRep = getRepresentativeAndAddElementIfNeeded(elem2);

		if (e1OldRep == e2OldRep) {
			// already equal --> nothing to do
			return false;
		}

		// merge the equivalence classes
		mElementTVER.reportEquality(elem1, elem2);

		final ELEM newRep = mElementTVER.getRepresentative(elem1);


		/*
		 * make copies of the ccpar and ccchild maps -- we need the old versions for congruence propagations
		 * (but we dont want to update after the propagations because this would hinder us from doing a lot of sanity
		 *   checks)
		 */
		final NestedMap2<ELEM, ELEM, Set<ELEM>> oldCcPar = ccparDeepCopy(mFunctionToRepresentativeToCcPars);
		final NestedMap2<ELEM, ELEM, Set<List<ELEM>>> oldCcChild =
				ccchildDeepCopy(mFunctionToRepresentativeToCcChildren);

		// update ccpar and ccchild sets
		updateCcparAndCcChildren(e1OldRep, e2OldRep, newRep);

		// do forward congruence propagations
		for (final Set<ELEM> eqc
				:
			mAllFunctions.stream().map(mElementTVER::getEquivalenceClass).collect(Collectors.toSet())) {

			for (final Entry<ELEM, ELEM> funcPair
					: CrossProducts.binarySelectiveCrossProduct(eqc, true, true)) {
				final Set<ELEM> e1CcPars = getCcPars(funcPair.getKey(), e1OldRep, oldCcPar);
				final Set<ELEM> e2CcPars = getCcPars(funcPair.getValue(), e2OldRep, oldCcPar);

				if (e1CcPars == null || e2CcPars == null) {
					// nothing to do
					continue;
				}

				final Set<ELEM> e1CcParsCopy = new HashSet<>(e1CcPars);
				final Set<ELEM> e2CcParsCopy = new HashSet<>(e2CcPars);

				// need to make copies because reportEqualityRec inside may modify the sets..
				for (final ELEM ccpar1 : e1CcParsCopy) {
					for (final ELEM ccpar2 : e2CcParsCopy) {
						// insert forward congruence
						if (argumentsAreCongruent(ccpar1, ccpar2)) {
							reportEqualityRec(ccpar1, ccpar2);
						}

						/*
						 * insert some backward congruences:
						 *
						 * say we knew before f(x1, x2) != g(y1, y2), and f = g. now we are reporting x1 = y1
						 *  --> then we need to propagate x2 != y2 now.
						 */
						if (getEqualityStatus(ccpar1, ccpar2) == EqualityStatus.NOT_EQUAL) {
							final int onlyDifferentPos = getOnlyUnconstrainedPos(ccpar1.getArguments(),
									ccpar2.getArguments());
							if (onlyDifferentPos != -1) {
								reportDisequalityRec(ccpar1.getArguments().get(onlyDifferentPos),
										ccpar2.getArguments().get(onlyDifferentPos),
										oldCcChild);
							}
						}
					}
				}
			}
		}

		/*
		 * do some more backward congruence propagations (see method documentation) we
		 * have two symmetric cases
		 */
		propagateDisequalities(e1OldRep, e2OldRep, oldCcChild);
		propagateDisequalities(e2OldRep, e1OldRep, oldCcChild);

		assert elem1.isFunction() == elem2.isFunction();
		if (elem1.isFunction()) {
			/*
			 * congruence propagations: if we are adding f = g then we can propagate f(x) =
			 * g(x) for all nodes of that form we know.
			 *
			 */
			for (final ELEM funcApp1 : mFunctionToFuncApps.getImage(elem1)) {
				for (final ELEM funcApp2 : mFunctionToFuncApps.getImage(elem2)) {
					if (funcApp1 == funcApp2) {
						continue;
					}
					if (argumentsAreCongruent(funcApp1, funcApp2)) {
						reportEquality(funcApp1, funcApp2);
					}
				}
			}
			updateInconsistencyStatus();
		}
		return true;
	}

	/**
	 * Called when element equivalence classes have been merged, and we therefore need to update the maps that have
	 * entries that need to be representatives (currently the maps for ccpars and ccchildren)
	 *
	 * @param e1OldRep
	 * @param e2OldRep
	 * @param newRep
	 */
	private void updateCcparAndCcChildren(final ELEM e1OldRep, final ELEM e2OldRep, final ELEM newRep) {
		for (final ELEM func : mAllFunctions) {
			final Set<ELEM> e1CcPars = getCcPars(func, e1OldRep, true);
			final Set<ELEM> e2CcPars = getCcPars(func, e2OldRep, true);

			final Set<List<ELEM>> e1CcChildren = mFunctionToRepresentativeToCcChildren.get(func, e1OldRep);
			final Set<List<ELEM>> e2CcChildren = mFunctionToRepresentativeToCcChildren.get(func, e2OldRep);

			// update CcPars and ccChildren -- add the elements in-place according to which element is the
			// new representative
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

	protected NestedMap2<ELEM, ELEM, Set<List<ELEM>>> ccchildDeepCopy(
			final NestedMap2<ELEM, ELEM, Set<List<ELEM>>> functionToRepresentativeToCcChildren) {
		final NestedMap2<ELEM, ELEM, Set<List<ELEM>>> result = new NestedMap2<>();
		for (final ELEM func : functionToRepresentativeToCcChildren.keySet()) {
			for (final ELEM rep : functionToRepresentativeToCcChildren.get(func).keySet()) {
				final HashSet<List<ELEM>> newSet = new HashSet<>();
				result.put(func, rep, newSet);
				for (final List<ELEM> ccchild : functionToRepresentativeToCcChildren.get(func, rep)) {
					newSet.add(new ArrayList<>(ccchild));
				}
			}
		}
		return result;
	}

	private NestedMap2<ELEM, ELEM, Set<ELEM>> ccparDeepCopy(
			final NestedMap2<ELEM, ELEM, Set<ELEM>> functionToRepresentativeToCcPars) {
		final NestedMap2<ELEM, ELEM, Set<ELEM>> result = new NestedMap2<>();
		for (final ELEM func : functionToRepresentativeToCcPars.keySet()) {
			for (final ELEM rep : functionToRepresentativeToCcPars.get(func).keySet()) {
				final HashSet<ELEM> newset = new HashSet<>(functionToRepresentativeToCcPars.get(func, rep));
				result.put(func, rep, newset);
			}
		}
		return result;
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
		if (elem.isFunction()) {
			mAllFunctions.add(elem);
		}

		if (!elem.isFunctionApplication()) {
			// nothing to do
			assert mElementTVER.getRepresentative(elem) != null : "this method assumes that elem has been added "
					+ "already";
			return;
		}

		mFunctionToFuncApps.addPair(elem.getAppliedFunction(), elem);
//		addFunction(elem.getAppliedFunction());
//		addElement(elem.getAppliedFunction());

		addFunctionElement(elem.getAppliedFunction());

		addToCcChildren(elem, elem.getArguments());

		for (final ELEM arg : elem.getArguments()) {			addElement(arg);
			addToCcPar(arg, elem);
			mElementToParents.addPair(arg, elem);
		}

		/*
		 * As the new element is a function application, we might be able to infer
		 * equalities for it through congruence.
		 */
		for (final ELEM equivalentFunction : mElementTVER.getEquivalenceClass(elem.getAppliedFunction())) {
			Set<ELEM> candidateSet = null;

			for (int i = 0; i < elem.getArguments().size(); i++) {
				final ELEM argRep = mElementTVER.getRepresentative(elem.getArguments().get(i));
				final Set<ELEM> newCandidates = getCcParsForArgumentPosition(equivalentFunction, argRep, i);
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



		assert sanityCheck();
	}

	/**
	 * This method is subtly different from addElement..
	 *
	 * @param appliedFunction
	 */
	private void addFunctionElement(final ELEM elem) {
		assert elem.isFunction();
		mElementTVER.addElement(elem);
		/*
		 *  it is important to look up mAllFunctions here, not check the result of mElementTVER.addElement because this
		 *  method might have been called from a constructor of this class that initialized mElementTVER but still needs
		 *   to register the elements
		 */
		if (!mAllFunctions.contains(elem)) {
			registerNewElement(elem);
		}
	}

	/**
	 * Retrieve CcPars of elem for function func that are parents for argument
	 * position i.
	 *
	 * @param equivalentFunction
	 * @param argRep
	 * @param i
	 * @return
	 */
	protected Set<ELEM> getCcParsForArgumentPosition(final ELEM func, final ELEM elem, final int i) {
		/*
		 * we take the ccpars from elem's equivalence class, but we filter, such that we only keep those ccpars that
		 * have an element of the equivalence class at argument position i.
		 */
		final Set<ELEM> result = mFunctionToRepresentativeToCcPars.get(func, elem);
		if (result == null) {
			return Collections.emptySet();
		}
		return result.stream().filter(par -> mElementTVER.getRepresentative(par.getArguments().get(i)).equals(elem))
				.collect(Collectors.toSet());
	}

	protected void updateInconsistencyStatus() {
		mIsInconsistent |= mElementTVER.isInconsistent();
	}

	/**
	 * Assumes that a disequality between the given elements has just been
	 * introduced. Does the propagations that follow from that disequality and the
	 * function congruence axiom.
	 *
	 * @param e1
	 * @param e2
	 * @param oldCcChild
	 */
	private void doBackwardCongruencePropagations(final ELEM e1, final ELEM e2,
			final NestedMap2<ELEM, ELEM, Set<List<ELEM>>> oldCcChild) {
		for (final Set<ELEM> eqc
				:
			mAllFunctions.stream().map(mElementTVER::getEquivalenceClass).collect(Collectors.toSet())) {

			for (final Entry<ELEM, ELEM> pair
					:
					CrossProducts.binarySelectiveCrossProduct(eqc, true, true).entrySet()) {

				final Set<List<ELEM>> e1CcChildren = getCcChildren(pair.getKey(), mElementTVER.getRepresentative(e1),
						oldCcChild);
				final Set<List<ELEM>> e2CcChildren = getCcChildren(pair.getValue(), mElementTVER.getRepresentative(e2),
						oldCcChild);

				for (final List<ELEM> ccChildList1 : e1CcChildren) {
					for (final List<ELEM> ccChildList2 : e2CcChildren) {
						final int onlyUnconstrainedPos = getOnlyUnconstrainedPos(ccChildList1, ccChildList2);
						if (onlyUnconstrainedPos != -1) {
							reportDisequalityRec(ccChildList1.get(onlyUnconstrainedPos),
									ccChildList2.get(onlyUnconstrainedPos), oldCcChild);
						}
					}
				}
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
	private void propagateDisequalities(final ELEM e1OldRep, final ELEM e2OldRep,
			final NestedMap2<ELEM, ELEM, Set<List<ELEM>>> oldCcChild) {
		for (final ELEM repUnequalToE1 : mElementTVER.getRepresentativesUnequalTo(e1OldRep)) {
			for (final Set<ELEM> eqc
					:
						mAllFunctions.stream().map(mElementTVER::getEquivalenceClass).collect(Collectors.toSet())) {
				for (final Entry<ELEM, ELEM> pair
						:
						CrossProducts.binarySelectiveCrossProduct(eqc, true, true).entrySet()) {
					final Set<ELEM> funcApps1 = getFunctionApplicationsInSameEquivalenceClass(pair.getKey(),
							repUnequalToE1);
					final Set<ELEM> funcApps2 = getFunctionApplicationsInSameEquivalenceClass(pair.getValue(),
							e2OldRep);

					if (funcApps1 == null || funcApps2 == null) {
						// nothing to do
						continue;
					}

					for (final ELEM ccpar1 : funcApps1) {
						for (final ELEM ccpar2 : funcApps2) {
							final int onlyDifferentPos = getOnlyUnconstrainedPos(ccpar1.getArguments(),
									ccpar2.getArguments());
							if (onlyDifferentPos != -1) {
								reportDisequalityRec(ccpar1.getArguments().get(onlyDifferentPos),
										ccpar2.getArguments().get(onlyDifferentPos),
										oldCcChild);
							}
						}
					}
				}
			}
		}
	}

//	public ELEM getRepresentativeAndAddFunctionIfNeeded(final ELEM func) {
//		addFunction(func);
//		return mFunctionTVER.getRepresentative(func);
//	}

	public ELEM getRepresentativeAndAddElementIfNeeded(final ELEM elem) {
		addElement(elem);
		return mElementTVER.getRepresentative(elem);
	}

	public ELEM getRepresentativeFunction(final ELEM func) {
		assert mAllFunctions.contains(func);
		final ELEM result = mElementTVER.getRepresentative(func);
		if (result == null) {
			throw new IllegalArgumentException(
					"Use this method only for elements that you now have been added " + "already");
		}
		assert result.isFunction();
		return result;
	}

	public ELEM getRepresentativeElement(final ELEM elem) {
		final ELEM result = mElementTVER.getRepresentative(elem);
		if (result == null) {
			throw new IllegalArgumentException(
					"Use this method only for elements that you now have been added " + "already");
		}
		return result;

	}

//	public boolean removeFunction(final ELEM func) {
//		if (mIsInconsistent) {
//			throw new IllegalStateException();
//		}
//		if (!hasFunction(func)) {
//			return false;
//		}
//
//
//		// remove all elements that depend on the function
//		final Set<ELEM> funcAppsWithFuncCopy = new HashSet<>(mFunctionToFuncApps.getImage(func));
//		for (final ELEM funcApp : funcAppsWithFuncCopy) {
//			removeElement(funcApp);
//		}
//
//		// remove from the function equivalence relation
////		mFunctionTVER.removeElement(func);
//		mElementTVER.removeElement(func);
//
//		mFunctionToRepresentativeToCcPars.remove(func);
//		mFunctionToRepresentativeToCcChildren.remove(func);
//		mFunctionToFuncApps.removeDomainElement(func);
//		return true;
//	}

	public boolean removeElement(final ELEM elem) {
		if (mIsInconsistent) {
			throw new IllegalStateException();
		}
		if (!hasElement(elem)) {
			return false;
		}

		purgeElem(elem);

		/*
		 * recursive call: if an element is removed, all the function applications that have it as an argument are
		 * removed, too
		 */
		for (final ELEM parent : new HashSet<>(mElementToParents.getImage(elem))) {
			removeElement(parent);
		}
		mElementToParents.removeDomainElement(elem);
		mElementToParents.removeRangeElement(elem);


		if (elem.isFunction()) {
			// remove all elements that depend on the function
			final Set<ELEM> funcAppsWithFuncCopy = new HashSet<>(mFunctionToFuncApps.getImage(elem));
			for (final ELEM funcApp : funcAppsWithFuncCopy) {
				removeElement(funcApp);
			}

			mFunctionToRepresentativeToCcPars.remove(elem);
			mFunctionToRepresentativeToCcChildren.remove(elem);
			mFunctionToFuncApps.removeDomainElement(elem);
		}

		assert elementIsFullyRemoved(elem);
		return true;
	}

	/**
	 * Remove the given element from all data structures where we store it, but don't do any recursive calls for
	 * removing dependent elements, and spare the data structures that are needed for those calls.
	 *
	 * @param elem
	 * @return the representative after removal of the equivalence where elem was in, null if elem was alone in its
	 * 	equivalence class
	 */
	protected ELEM purgeElem(final ELEM elem) {
		final boolean elemWasRepresentative = mElementTVER.isRepresentative(elem);
		final ELEM newRep = mElementTVER.removeElement(elem);

		/*
		 * deal with the maps that may only have elem representatives as entries
		 */
		if (newRep == null) {
			// elem was the only element of its equivalence class
			mFunctionToRepresentativeToCcPars.removeK2(elem);
			mFunctionToRepresentativeToCcChildren.removeK2(elem);

		} else if (elemWasRepresentative) {
			// elem was the representative, and not the only element of its equivalence class
			mFunctionToRepresentativeToCcPars.replaceK2(elem, newRep, false);
			mFunctionToRepresentativeToCcChildren.replaceK2(elem, newRep, false);
		} else {
			// elem was not the representative of its equivalence class

		}

		/*
		 * clean the entries that not only store representatives
		 */
		final NestedMap2<ELEM, ELEM, Set<List<ELEM>>> ccchildrencpy =
				new NestedMap2<>(mFunctionToRepresentativeToCcChildren);
		for (final ELEM func : ccchildrencpy.keySet()) {
			for (final ELEM rep : ccchildrencpy.get(func).keySet()) {
				final Set<List<ELEM>> lists = mFunctionToRepresentativeToCcChildren.get(func, rep);
				final Set<List<ELEM>> listscpy = new HashSet<>(lists);
				for (final List<ELEM> list : listscpy) {
					if (list.contains(elem)) {
						lists.remove(list);
					}
				}
			}
		}
		final NestedMap2<ELEM, ELEM, Set<ELEM>> ccparscpy = new NestedMap2<>(mFunctionToRepresentativeToCcPars);
		for (final ELEM func : ccparscpy.keySet()) {
			for (final ELEM rep : ccparscpy.get(func).keySet()) {
				mFunctionToRepresentativeToCcPars.get(func, rep).remove(elem);
			}
		}

		mFunctionToFuncApps.removeRangeElement(elem);

		return newRep;
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
		for (final Entry<ELEM, ELEM> en : mFunctionToFuncApps.entrySet()) {
			if (en.getValue().equals(elem)) {
				assert false;
				return false;
			}
		}

		for (final Entry<ELEM, ELEM> en : mElementToParents) {
			if (en.getKey().equals(elem) || en.getValue().equals(elem)) {
				assert false;
				return false;
			}
		}

		for (final Triple<ELEM, ELEM, Set<List<ELEM>>> en : mFunctionToRepresentativeToCcChildren.entrySet()) {
			if (en.getSecond().equals(elem)) {
				assert false;
				return false;
			}
			if (en.getThird().stream().anyMatch(list -> list.contains(elem))) {
				assert false;
				return false;
			}
		}

		for (final Triple<ELEM, ELEM, Set<ELEM>> en : mFunctionToRepresentativeToCcPars.entrySet()) {
			if (en.getSecond().equals(elem)) {
				assert false;
				return false;
			}
			if (en.getThird().contains(elem)) {
				assert false;
				return false;
			}
		}

		if (mAllFunctions.contains(elem)) {
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
//		final ThreeValuedEquivalenceRelation<ELEM> newFunctionTver = thisAligned.mFunctionTVER
//				.join(otherAligned.mFunctionTVER);

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
//		other.getAllFunctions().stream().forEach(func -> result.addFunction(func));

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
//		for (final Entry<ELEM, ELEM> eq : otherAligned.getSupportingFunctionEqualities().entrySet()) {
//			if (thisAligned.isInconsistent()) {
//				return new CongruenceClosure<>(true);
//			}
//			thisAligned.reportFunctionEquality(eq.getKey(), eq.getValue());
//		}
		for (final Entry<ELEM, ELEM> deq : otherAligned.getElementDisequalities()) {
			if (thisAligned.isInconsistent()) {
				return new CongruenceClosure<>(true);
			}
			thisAligned.reportDisequality(deq.getKey(), deq.getValue());
		}
//		for (final Entry<ELEM, ELEM> deq : otherAligned.getFunctionDisequalities()) {
//			if (thisAligned.isInconsistent()) {
//				return new CongruenceClosure<>(true);
//			}
//			thisAligned.reportFunctionDisequality(deq.getKey(), deq.getValue());
//		}

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
//		assert thisAligned.getAllFunctions().equals(otherAligned.getAllFunctions());

		if (!isPartitionStronger(thisAligned.mElementTVER, otherAligned.mElementTVER)) {
			return false;
		}
//		if (!isPartitionStronger(thisAligned.mFunctionTVER, otherAligned.mFunctionTVER)) {
//			return false;
//		}

		/*
		 * We check if each disequality that holds in "other" also holds in "this".
		 */
		if (!areDisequalitiesStrongerThan(thisAligned.mElementTVER, otherAligned.mElementTVER)) {
			return false;
		}
//		if (!areDisequalitiesStrongerThan(thisAligned.mFunctionTVER, otherAligned.mFunctionTVER)) {
//			return false;
//		}
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

//	public EqualityStatus getEqualityStatus(final ELEM elem1, final ELEM elem2) {
//		return mFunctionTVER.getEqualityStatus(elem1, elem2);
//	}

	public EqualityStatus getEqualityStatus(final ELEM elem1, final ELEM elem2) {
		return mElementTVER.getEqualityStatus(elem1, elem2);
	}

	public Set<ELEM> getAllElements() {
		return Collections.unmodifiableSet(mElementTVER.getAllElements());
	}

	public Set<ELEM> getAllFunctions() {
		return Collections.unmodifiableSet(mAllFunctions);
	}

	public boolean isInconsistent() {
		return mIsInconsistent;
	}

	public boolean argumentsAreCongruent(final ELEM funcApp1, final ELEM funcApp2) {
		return argumentsAreCongruent(funcApp1, funcApp2, true);
	}

	/**
	 *
	 * @param funcApp1 function application element
	 * @param funcApp2 function application element
	 * @param forceThatFunctionsAreEqual true iff we expect that the given functions are equal according to the current
	 * 		state
	 * @return true iff each two argument elements at the same position in the
	 *         argument list are equal according to the current state of mElemenTVER
	 */
	public boolean argumentsAreCongruent(final ELEM funcApp1, final ELEM funcApp2,
			final boolean forceThatFunctionsAreEqual) {
		assert funcApp1.isFunctionApplication() && funcApp2.isFunctionApplication();
		assert !forceThatFunctionsAreEqual || mElementTVER.getEqualityStatus(funcApp1.getAppliedFunction(),
				funcApp2.getAppliedFunction()) == EqualityStatus.EQUAL;
		assert funcApp1.getArguments().size() == funcApp2.getArguments().size();

		return argumentsAreCongruent(funcApp1.getArguments(), funcApp2.getArguments());
	}

	protected boolean argumentsAreCongruent(final List<ELEM> argList1, final List<ELEM> argList2) {
		for (int i = 0; i < argList1.size(); i++) {
			if (mElementTVER.getEqualityStatus(argList1.get(i), argList2.get(i)) != EqualityStatus.EQUAL) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Checks if all entries of the given lists are equal (at the matching list
	 * index) on all positions except for one. Returns that position if it exists,
	 * -1 otherwise.
	 *
	 * @param ccChild1
	 * @param ccChild2
	 * @return the only position in where the equality status between the entries of
	 *         the lists is UNKOWN according to mElementTVER when all other
	 *         positions have status EQUAL, -1 if no such position exists
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
			} else if (mElementTVER.getEqualityStatus(ccChildList1.get(i),
					ccChildList2.get(i)) == EqualityStatus.NOT_EQUAL) {
				return -1;
			}
		}
		return result;
	}

	private Set<ELEM> getFunctionApplicationsInSameEquivalenceClass(final ELEM func, final ELEM elem) {
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
		final ELEM func = funcApp.getAppliedFunction();
		final ELEM elemRep = getRepresentativeElement(elem);

		Set<ELEM> ccpars = mFunctionToRepresentativeToCcPars.get(func, elemRep);
		if (ccpars == null) {
			ccpars = new HashSet<>();
			mFunctionToRepresentativeToCcPars.put(func, elemRep, ccpars);
		}
		ccpars.add(funcApp);
		assert ccparsFunctionMatchesFuncApps();
	}

	private boolean ccparsFunctionMatchesFuncApps() {
		for (final Triple<ELEM, ELEM, Set<ELEM>> triple : mFunctionToRepresentativeToCcPars.entrySet()) {
			for (final ELEM setElem : triple.getThird()) {
				if (!setElem.isFunctionApplication()) {
					assert false;
					return false;
				}
				if (!setElem.getAppliedFunction().equals(triple.getFirst())) {
					assert false;
					return false;
				}
			}
		}
		return true;
	}

	private void addToCcChildren(final ELEM elem, final List<ELEM> arguments) {
		assert elem.isFunctionApplication();
		final ELEM funcRep = getRepresentativeFunction(elem.getAppliedFunction());
		final ELEM elemRep = getRepresentativeElement(elem);

		Set<List<ELEM>> ccChildrenSet = mFunctionToRepresentativeToCcChildren.get(funcRep, elemRep);

		if (ccChildrenSet == null) {
			ccChildrenSet = new HashSet<>();
			mFunctionToRepresentativeToCcChildren.put(funcRep, elemRep, ccChildrenSet);
		}
		ccChildrenSet.add(arguments);
	}

	/**
	 * mFunctionToRepresentativeToCcPars only speaks about representatives (in the
	 * second entry). This is called when the given ELEM is no more a representative
	 * an thus its whole entry in the nested map can be removed.
	 *
	 * @param e2OldRep
	 * @param func
	 */
	private void removeFromCcpars(final ELEM e2OldRep, final ELEM func) {
		if (mFunctionToRepresentativeToCcPars.get(func) == null) {
			// no entry for func present --> do nothing
			return;
		}
		mFunctionToRepresentativeToCcPars.remove(func, e2OldRep);
	}

	private void removeFromCcChildren(final ELEM elem, final ELEM func) {
		if (mFunctionToRepresentativeToCcChildren.get(func) == null) {
			// no entry for func present --> do nothing
			return;
		}
		mFunctionToRepresentativeToCcChildren.remove(func, elem);
	}


	public Set<ELEM> getCcPars(final ELEM func, final ELEM newRep) {
		return getCcPars(func, newRep, false);
	}


	private static <ELEM> Set<ELEM> getCcPars(final ELEM func, final ELEM newRep,
			final NestedMap2<ELEM, ELEM, Set<ELEM>> oldCcPar) {
		Set<ELEM> res = oldCcPar.get(func, newRep);
		if (res == null) {
			res = new HashSet<>();
			oldCcPar.put(func, newRep, res);
		}
		return res;

	}

	/**
	 * Retrieves the ccpar map for the given function and element. Creates one if there is none..
	 *
	 * Note that this method can introduce new entries at the "second" position of the ccpars nested map, this may
	 * violate our invariant that that position only contains representatives. This may be done temporarily, in that
	 * case the flag should be used, otherwise an assertion checks that newRep is a representative.
	 *
	 * @param func
	 * @param newRep
	 * @param allowNonrepElem
	 * @return
	 */
	private Set<ELEM> getCcPars(final ELEM func, final ELEM newRep, final boolean allowNonRepresentatives) {
		assert mElementTVER.isRepresentative(newRep) || allowNonRepresentatives;
		Set<ELEM> res = mFunctionToRepresentativeToCcPars.get(func, newRep);
		if (res == null) {
			res = new HashSet<>();
			mFunctionToRepresentativeToCcPars.put(func, newRep, res);
		}
		return res;
	}

	protected Set<List<ELEM>> getCcChildren(final ELEM func, final ELEM rep,
			final NestedMap2<ELEM, ELEM, Set<List<ELEM>>> oldCcChild) {
		return getCcChildren(func, rep, oldCcChild, false);
	}

	protected Set<List<ELEM>> getCcChildren(final ELEM func, final ELEM rep,
			final NestedMap2<ELEM, ELEM, Set<List<ELEM>>> oldCcChild, final boolean allowNonRepresentatives) {
		assert allowNonRepresentatives || mElementTVER.isRepresentative(rep);
		Set<List<ELEM>> res = oldCcChild.get(func, rep);
		if (res == null) {
			res = new HashSet<>();
			oldCcChild.put(func, rep, res);
		}
		return res;
	}

	private Set<List<ELEM>> getCcChildren(final ELEM func, final ELEM el) {
		final ELEM rep = mElementTVER.getRepresentative(el);
		Set<List<ELEM>> res = mFunctionToRepresentativeToCcChildren.get(func, rep);
		if (res == null) {
			res = new HashSet<>();
			mFunctionToRepresentativeToCcChildren.put(func, rep, res);
		}
		return res;
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

//		if (mFunctionTVER.isInconsistent()) {
//					assert false;
//					return false;
//		}

		/*
		 * check that all elements in mAllFunctions are indeed functions
		 */
		for (final ELEM f : mAllFunctions) {
			if (!f.isFunction()) {
				assert false;
				return false;
			}
		}


		for (final Triple<ELEM, ELEM, Set<ELEM>> repFuncCcPars : mFunctionToRepresentativeToCcPars.entrySet()) {

			// the first entry must be a function
			if (!repFuncCcPars.getFirst().isFunction()) {
				assert false;
				return false;
			}

			if (!mElementTVER.isRepresentative(repFuncCcPars.getSecond())) {
				assert false;
				return false;
			}

			// every element in the ccpars set must be a function application of the function that the ccpars set is for
			if (repFuncCcPars.getThird().stream()
					.anyMatch(elem -> (!elem.isFunctionApplication()
							|| !elem.getAppliedFunction().equals(repFuncCcPars.getFirst())))) {
				assert false;
				return false;
			}
		}

		for (final Triple<ELEM, ELEM, Set<List<ELEM>>> repFuncCcChildren : mFunctionToRepresentativeToCcChildren
				.entrySet()) {
			if (!mElementTVER.isRepresentative(repFuncCcChildren.getSecond())) {
				assert false;
				return false;
			}
		}

		if (!mIsInconsistent) {
			if (mElementTVER.isInconsistent()) {
				assert false;
				return false;
			}
//			if (mFunctionTVER.isInconsistent()) {
//				assert false;
//				return false;
//			}
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

//	public Map<ELEM, ELEM> getSupportingFunctionEqualities() {
//		return mFunctionTVER.getSupportingEqualities();
//	}

	public HashRelation<ELEM, ELEM> getElementDisequalities() {
		return mElementTVER.getDisequalities();
	}

//	public HashRelation<ELEM, ELEM> getFunctionDisequalities() {
//		return mFunctionTVER.getDisequalities();
//	}

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
//		sb.append("\n");

//		sb.append("Function equivalences:");
//		sb.append(mFunctionTVER);

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
	 */
	public void transformElementsAndFunctions(final Function<ELEM, ELEM> elemTransformer,
			final Function<ELEM, ELEM> functionTransformer) {
		assert sanitizeTransformer(elemTransformer, getAllElements()) : "we assume that the transformer does not "
				+ "produce elements that were in the relation before!";
//		assert sanitizeTransformer(functionTransformer, getAllFunctions()) : "we assume that the transformer does not "
//				+ "produce elements that were in the relation before!";

		mElementTVER.transformElements(elemTransformer);
//		mFunctionTVER.transformElements(functionTransformer);

		final NestedMap2<ELEM, ELEM, Set<ELEM>> ccparsCopy = new NestedMap2<>(mFunctionToRepresentativeToCcPars);
		for (final Triple<ELEM, ELEM, Set<ELEM>> triple : ccparsCopy.entrySet()) {
			mFunctionToRepresentativeToCcPars.remove(triple.getFirst(), triple.getSecond());
			mFunctionToRepresentativeToCcPars.put(functionTransformer.apply(triple.getFirst()),
					elemTransformer.apply(triple.getSecond()),
					triple.getThird().stream().map(elemTransformer).collect(Collectors.toSet()));
		}


		final NestedMap2<ELEM, ELEM, Set<List<ELEM>>> ccChildrenCopy =
				new NestedMap2<>(mFunctionToRepresentativeToCcChildren);
		for (final Triple<ELEM, ELEM, Set<List<ELEM>>> triple : ccChildrenCopy.entrySet()) {
			mFunctionToRepresentativeToCcChildren.remove(triple.getFirst(), triple.getSecond());
			mFunctionToRepresentativeToCcChildren.put(functionTransformer.apply(triple.getFirst()),
					elemTransformer.apply(triple.getSecond()),
					triple.getThird().stream()
						.map(list ->
							list.stream().map(elemTransformer).collect(Collectors.toList()))
						.collect(Collectors.toSet()));
		}

		final HashRelation<ELEM, ELEM> ftfaCopy = new HashRelation<>(mFunctionToFuncApps);
		for (final Entry<ELEM, ELEM> en : ftfaCopy.entrySet()) {
			mFunctionToFuncApps.removePair(en.getKey(), en.getValue());
			mFunctionToFuncApps.addPair(functionTransformer.apply(en.getKey()), elemTransformer.apply(en.getValue()));
		}

		final HashRelation<ELEM, ELEM> etpCopy = new HashRelation<>(mElementToParents);
		for (final Entry<ELEM, ELEM> en : etpCopy.entrySet()) {
			mElementToParents.removePair(en.getKey(), en.getValue());
			mElementToParents.addPair(elemTransformer.apply(en.getKey()), elemTransformer.apply(en.getValue()));
		}
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

	public boolean hasFunction(final ELEM elem) {
		return getAllFunctions().contains(elem);
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

	@Override
	public boolean equals(final Object obj) {
		// TODO Auto-generated method stub
		return super.equals(obj);
	}

	@Override
	public int hashCode() {
		// TODO Auto-generated method stub
		return super.hashCode();
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
//		final ThreeValuedEquivalenceRelation<ELEM> newFunctionPartition =
//				new ThreeValuedEquivalenceRelation<>(this.mFunctionTVER);
		return new CongruenceClosure<>(newElemPartition);
	}

	public Collection<ELEM> getAllElementRepresentatives() {
		return mElementTVER.getAllRepresentatives();
	}
}
