package de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * auxilliary data related to congruence classes
 */
public class CcAuxData<ELEM extends ICongruenceClosureElement<ELEM>> {

	/**
	 * CongruenceClosure instance this provides the auxiliary data for.
	 */
	private final CongruenceClosure<ELEM> mCongruenceClosure;

	private final HashRelation<ELEM, ELEM> mAfCcPars;
	private final HashRelation<ELEM, ELEM> mArgCcPars;

	private final Map<ELEM, HashRelation<ELEM, ELEM>> mCcChildren;

	/**
	 * normally we only allow get..(elem) calls when elem is a representative of the enclosing CongruenceClosure
	 * this flag deactivates those checks
	 */
	private final boolean mOmitRepresentativeChecks;

	CcAuxData(final CongruenceClosure<ELEM> congruenceClosure) {
		mCongruenceClosure = congruenceClosure;
		mAfCcPars = new HashRelation<>();
		mArgCcPars = new HashRelation<>();
		mCcChildren = new HashMap<>();
		mOmitRepresentativeChecks = false;
	}

	public CcAuxData(final CongruenceClosure<ELEM> congruenceClosure, final CcAuxData<ELEM> auxData,
			final boolean omitRepresentativeChecks) {
		mCongruenceClosure = congruenceClosure;
		mAfCcPars = new HashRelation<>(auxData.mAfCcPars);
		mArgCcPars = new HashRelation<>(auxData.mArgCcPars);
		mCcChildren = new HashMap<>();
		for (final Entry<ELEM, HashRelation<ELEM, ELEM>> en : auxData.mCcChildren.entrySet()) {
			mCcChildren.put(en.getKey(), new HashRelation<>(en.getValue()));
		}
		mOmitRepresentativeChecks = omitRepresentativeChecks;
	}

	CcAuxData(final CongruenceClosure<ELEM> congruenceClosure, final CcAuxData<ELEM> auxData) {
		this(congruenceClosure, auxData, false);
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
	Pair<HashRelation<ELEM, ELEM>, HashRelation<ELEM, ELEM>> updateAndGetPropagationsOnMerge(
			final ELEM e1, final ELEM e2, final ELEM e1OldRep, final ELEM e2OldRep,
			final Set<ELEM> oldUnequalRepsForElem1, final Set<ELEM> oldUnequalRepsForElem2) {

		final ELEM newRep = mCongruenceClosure.mElementTVER.getRepresentative(e1);
		assert mCongruenceClosure.mElementTVER.getRepresentative(e2) == newRep : "we merged before calling this method, right?";

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
					assert e.isFunctionApplication();
					mAfCcPars.addPair(newRep, e);
				}
			}
			final Set<ELEM> oldArg2 = mArgCcPars.removeDomainElement(e2OldRep);
			if (oldArg2 != null) {
				for (final ELEM e : oldArg2) {
					assert e.isFunctionApplication();
					mArgCcPars.addPair(newRep, e);
				}
			}
		} else {
			assert newRep == e2OldRep;
			final Set<ELEM> oldAf1 = mAfCcPars.removeDomainElement(e1OldRep);
			if (oldAf1 != null) {
				for (final ELEM e : oldAf1) {
					assert e.isFunctionApplication();
					mAfCcPars.addPair(newRep, e);
				}
			}
			final Set<ELEM> oldArg1 = mArgCcPars.removeDomainElement(e1OldRep);
			if (oldArg1 != null) {
				for (final ELEM e : oldArg1) {
					assert e.isFunctionApplication();
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

	private void collectCcParBasedPropagations(final Set<ELEM> parents1,
			final Set<ELEM> parents2, final HashRelation<ELEM, ELEM> congruentResult,
			final HashRelation<ELEM, ELEM> unequalResult) {
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
			if (mCongruenceClosure.hasElements(parent1.getAppliedFunction(), parent1.getArgument(),
					parent2.getAppliedFunction(), parent2.getArgument())
					&& mCongruenceClosure.getEqualityStatus(parent1.getAppliedFunction(), parent2.getAppliedFunction())
					== EqualityStatus.EQUAL
					&& mCongruenceClosure.getEqualityStatus(parent1.getArgument(), parent2.getArgument())
					== EqualityStatus.EQUAL) {

				congruentResult.addPair(parent1, parent2);
				continue;
			}

			/*
			 * bwcc (1)
			 */
			if (mCongruenceClosure.getEqualityStatus(parent1, parent2) == EqualityStatus.NOT_EQUAL) {
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
//			if (elem.isFunctionApplication()) {
			if (elem.isFunctionApplication() && mCcChildren.get(newRep) != null) {
				mCcChildren.get(newRep).removePair(elem.getAppliedFunction(), elem.getArgument());
			}
		}
	}

	HashRelation<ELEM, ELEM> registerNewElement(final ELEM elem) {
		assert elem.isFunctionApplication() : "right?..";

		final ELEM afRep = mCongruenceClosure.hasElement(elem.getAppliedFunction()) ?
				mCongruenceClosure.mElementTVER.getRepresentative(elem.getAppliedFunction()) :
					elem.getAppliedFunction();
		final ELEM argRep = mCongruenceClosure.hasElement(elem.getArgument()) ?
				mCongruenceClosure.mElementTVER.getRepresentative(elem.getArgument()) :
					elem.getArgument();


		final HashRelation<ELEM, ELEM> equalitiesToPropagate = new HashRelation<>();
		if (!mCongruenceClosure.isInconsistent()) {
			final Set<ELEM> afCcPars = mAfCcPars.getImage(afRep);
			final Set<ELEM> candidates = afCcPars.stream()
					.filter(afccpar ->
					(mCongruenceClosure.hasElement(argRep) &&
							mCongruenceClosure.hasElement(afccpar.getArgument()) &&
							mCongruenceClosure.getEqualityStatus(argRep, afccpar.getArgument()) == EqualityStatus.EQUAL)
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
		}


		//			assert mElementCurrentlyBeingRemoved == null
		//					|| !equalitiesToPropagate.entrySet().stream().map(en -> en.getValue())
		//						.anyMatch(c -> c.isFunctionApplication()
		//					&& (c.getAppliedFunction().equals(mElementCurrentlyBeingRemoved.getElem())
		//							|| c.getArgument().equals(mElementCurrentlyBeingRemoved.getElem())));

		mAfCcPars.addPair(afRep, elem);
		mArgCcPars.addPair(argRep, elem);

		// is it even possible that elem is not its own representative at this point??
		final ELEM elemRep = mCongruenceClosure.mElementTVER.getRepresentative(elem);

		updateCcChild(elemRep, elem.getAppliedFunction(), elem.getArgument());

		return equalitiesToPropagate;
	}

	private void updateCcChild(final ELEM elemRep, final ELEM appliedFunction,
			final ELEM argument) {
		HashRelation<ELEM, ELEM> elemCcc = mCcChildren.get(elemRep);
		if (elemCcc == null) {
			elemCcc = new HashRelation<>();
			mCcChildren.put(elemRep, elemCcc);
		}
		elemCcc.addPair(appliedFunction, argument);
	}

	public HashRelation<ELEM, ELEM> getPropagationsOnReportDisequality(final ELEM elem1, final ELEM elem2) {
		final HashRelation<ELEM, ELEM> result = new HashRelation<>();

		final ELEM e1Rep = mCongruenceClosure.mElementTVER.getRepresentative(elem1);
		final ELEM e2Rep = mCongruenceClosure.mElementTVER.getRepresentative(elem2);

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
		assert mOmitRepresentativeChecks || mCongruenceClosure.isRepresentative(rep);
		HashRelation<ELEM, ELEM> result = mCcChildren.get(rep);
		if (result == null) {
			result = new HashRelation<>();
			mCcChildren.put(rep, result);
		}
		return result;
	}

	private void addPropIfOneIsEqualOneIsUnconstrained(final ELEM af1,
			final ELEM arg1, final ELEM af2, final ELEM arg2,final HashRelation<ELEM, ELEM> result) {
		if (!mCongruenceClosure.hasElement(af1) || !mCongruenceClosure.hasElement(af2)
				|| !mCongruenceClosure.hasElement(arg1) || !mCongruenceClosure.hasElement(arg2)) {
			/*
			 *  it may happen that during a remove element we reach here and some map still has an element that is
			 *  being removed (if we added a propagation here, we would add the element back..)
			 */
			return;
		}

		final EqualityStatus equalityStatusOfAppliedFunctions =
				mCongruenceClosure.getEqualityStatus(af1, af2);
		final EqualityStatus equalityStatusOfArguments =
				mCongruenceClosure.getEqualityStatus(arg1, arg2);

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
		assert mOmitRepresentativeChecks || mCongruenceClosure.isRepresentative(elem);
		return mAfCcPars.getImage(elem);
	}

	public Collection<ELEM> getArgCcPars(final ELEM elem) {
		assert mOmitRepresentativeChecks || mCongruenceClosure.isRepresentative(elem);
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