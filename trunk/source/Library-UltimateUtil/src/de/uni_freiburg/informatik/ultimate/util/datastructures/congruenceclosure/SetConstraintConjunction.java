package de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;

/**
 * Represents a conjunction over single set constraints that all constrain the
 * same element.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ELEM>
 */
public class SetConstraintConjunction<ELEM extends ICongruenceClosureElement<ELEM>> {

	private ELEM mConstrainedElement;

	final CCLiteralSetConstraints<ELEM> mSurroundingCCSetConstraints;

	private final SetConstraintManager<ELEM> mSetConstraintManager;

	private Set<SetConstraint<ELEM>> mSetConstraints;

	private final SetConstraint<ELEM> mScWithOnlyLiterals;

	/**
	 * sufficient but not a necessary condition for inconsistency
	 */
	private boolean mIsInconsistent;

	/**
	 * special constructor for an inconsistent SetCc
	 *
	 * @param isInconsistent
	 */
	public SetConstraintConjunction(final boolean isInconsistent) {
		assert isInconsistent : "use other constructor in this case!!";
		mConstrainedElement = null;
		mIsInconsistent = true;
		mSetConstraints = null;
		mSurroundingCCSetConstraints = null;
		mScWithOnlyLiterals = null;
		mSetConstraintManager = null;
		assert sanityCheck();
	}

	public SetConstraintConjunction(final CCLiteralSetConstraints<ELEM> surroundingSetConstraints,
			final ELEM constrainedElement, final Collection<SetConstraint<ELEM>> setConstraintsRaw) {
		mConstrainedElement = constrainedElement;
		mSurroundingCCSetConstraints = surroundingSetConstraints;
		mSetConstraintManager = surroundingSetConstraints.getCongruenceClosure().getManager().getSetConstraintManager();

		final List<SetConstraint<ELEM>> onlyLits =
				setConstraintsRaw.stream().filter(SetConstraint::hasOnlyLiterals).collect(Collectors.toList());
		assert onlyLits.size() < 2;
		if (onlyLits.size() == 1) {
			mScWithOnlyLiterals = onlyLits.iterator().next();
		} else {
			mScWithOnlyLiterals = null;
		}

		mSetConstraints = Collections.unmodifiableSet(new HashSet<>(setConstraintsRaw));// new HashSet<>(setConstraints);
		assert sanityCheck();
	}

	/**
	 * copy constructor that may change surroundingCC..
	 *
	 * @param original
	 * @param surroundingCCSetConstraints
	 */
	public SetConstraintConjunction(final CCLiteralSetConstraints<ELEM> surroundingCCSetConstraints,
			final SetConstraintConjunction<ELEM> original) {
		mSurroundingCCSetConstraints = surroundingCCSetConstraints;
		mConstrainedElement = original.mConstrainedElement;
		mSetConstraintManager = original.mSetConstraintManager;

		mSetConstraints = Collections.unmodifiableSet(new HashSet<>(original.getSetConstraints()));
		mScWithOnlyLiterals  = original.mScWithOnlyLiterals;
		assert sanityCheck();
	}


	/**
	 * The given element is projected away. Assume it is not mConstrainedElement.
	 * Project it in the sets.
	 *
	 * @param elem
	 */
	public void projectAway(final ELEM elem) {
//		assert mSurroundingCCSetConstraints.getCongruenceClosure().isRepresentative(elem) : "right?..";
		assert !elem.equals(mConstrainedElement);

		/*
		 * remove constraints that have elem on their right hand side (a more precise
		 * alternative would be to introduce a dummy element, effectively an
		 * existentially quantified variable.. but we would have to introduce one for
		 * every projected element, right?..)
		 */
		final Set<SetConstraint<ELEM>> newSetConstraints = new HashSet<>();
		for (final SetConstraint<ELEM> sc : mSetConstraints) {
//			if (sc.containsElement(elem)) {
//				mSetConstraints.remove(sc);
//			}
			if (!sc.containsElement(elem)) {
				newSetConstraints.add(sc);
			}
		}
		mSetConstraints = newSetConstraints;
	}

	private Set<ELEM> getSingletonValues() {
		return mSetConstraintManager.getSingletonValues(mSetConstraints);
	}

	public boolean isTautological() {
		if (mIsInconsistent) {
			return false;
		}
		if (mSetConstraints.isEmpty()) {
			return true;
		}

		return false;
	}

	public boolean isInconsistent() {
		assert !mIsInconsistent || mSetConstraints == null;
		return mIsInconsistent || mSetConstraints.stream().anyMatch(sc -> sc.isInconsistent());
	}

	public CongruenceClosure<ELEM> getCongruenceClosure() {
		return mSurroundingCCSetConstraints.getCongruenceClosure();
	}

	public ELEM getConstrainedElement() {
		assert mConstrainedElement != null;
		return mConstrainedElement;
	}


	CcManager<ELEM> getCcManager() {
		return mSurroundingCCSetConstraints.getCongruenceClosure().getManager();
	}

	public Set<ELEM> getAllRhsElements() {
		final Set<ELEM> result = new HashSet<>();

		for (final SetConstraint<ELEM> sc : mSetConstraints) {
			result.addAll(sc.getElementSet());
		}

		return Collections.unmodifiableSet(result);
	}

	public Set<Set<ELEM>> getElementSets() {
		final Set<Set<ELEM>> result = new HashSet<>();

		for (final SetConstraint<ELEM> sc : mSetConstraints) {
			result.add(sc.getElementSet());
		}

		return Collections.unmodifiableSet(result);
	}

	@Override
	public String toString() {
		if (mIsInconsistent) {
			return "SetCc: False";
		}

		return "SetConstraintConjunction [ConstrainedElement=" + mConstrainedElement + ", mSetConstraints="
				+ mSetConstraints + "]";
	}

	public boolean hasOnlyLiterals() {
		return mScWithOnlyLiterals != null;
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> boolean hasOnlyLiterals(
			final Collection<SetConstraint<ELEM>> setConstraints) {
		return setConstraints.stream().anyMatch(sc -> sc.hasOnlyLiterals());
	}

	public Set<ELEM> getLiterals() {
		assert mScWithOnlyLiterals.getNonLiterals().isEmpty();
		return mScWithOnlyLiterals.getLiterals();
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> Set<ELEM> getLiterals(
			final Collection<SetConstraint<ELEM>> setConstraints) {
		assert setConstraints.stream().filter(sc -> sc.hasOnlyLiterals()).collect(Collectors.toSet()).size() == 1;
		for (final SetConstraint<ELEM> sc : setConstraints) {
			if (sc.hasOnlyLiterals()) {
				return sc.getLiterals();
			}
		}
		throw new IllegalStateException("check for hasOnlyLiterals before calling this");
	}

	public void expandVariableToLiterals(final CCLiteralSetConstraints<ELEM> surroundingSetConstraints, final ELEM elem,
			final Set<ELEM> literals) {
		assert !elem.isLiteral();
		assert getCongruenceClosure().isRepresentative(elem);

		boolean madeChanges = false;
		for (final SetConstraint<ELEM> sc : mSetConstraints) {
			madeChanges |= sc.expandVariableToLiterals(elem, literals);
		}

		if (madeChanges) {
			mSetConstraints = mSurroundingCCSetConstraints.getCongruenceClosure().getManager()
					.normalizeSetConstraintConjunction(surroundingSetConstraints, mSetConstraints);
		}
	}

	public void resetConstrainedElement(final ELEM elementRep) {
		mConstrainedElement = elementRep;
	}

	public Set<SetConstraint<ELEM>> getSetConstraints() {
		return Collections.unmodifiableSet(mSetConstraints);
	}

	public boolean sanityCheck() {
		if (mIsInconsistent) {
			if (mSurroundingCCSetConstraints == null) {
				// fine in this case, no further checks needed
				return true;
			}
			// check that inconsistency flag is set correctly
			if (!CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3) {
				if (!mSetConstraints.stream().anyMatch(sc -> sc.isInconsistent())) {
					assert false;
					return false;
				}
			}
		} else {
			// EDIT: new convention: mIsInconsistent flag is a sufficient but not a
			// necessary condition for
			// inconsistency
		}

		/*
		 * singleton values should be propagated as equalities and omitted from any SetConstraintConjunction
		 */
		if (!getSingletonValues().isEmpty()) {
			assert false;
			return false;
		}

		for (final SetConstraint<ELEM> conjunct : mSetConstraints) {
			if (!conjunct.sanityCheck()) {
				assert false;
				return false;
			}
		}
		if (mSurroundingCCSetConstraints.getCongruenceClosure() != null) {
			for (final SetConstraint<ELEM> conjunct : mSetConstraints) {
				// all must be representatives
				for (final ELEM el : conjunct.getElementSet()) {
					if (!mSurroundingCCSetConstraints.getCongruenceClosure().isRepresentative(el)) {
						assert false;
						return false;
					}
				}
			}
		}

		// check minimality of conjunction : all must be incomparable!
		if (!CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3) {
			for (final SetConstraint<ELEM> sc1 : mSetConstraints) {
				for (final SetConstraint<ELEM> sc2 : mSetConstraints) {
					if (sc1 == sc2) {
						continue;
					}

					if (mSetConstraintManager.isStrongerThan(sc1, sc2)) {
						assert false;
						return false;
					}
				}
			}
		}


		// check minimality: conjunction may not contain tautological elements
		for (final SetConstraint<ELEM> sc : mSetConstraints) {
			if (sc.containsElement(mConstrainedElement)) {
				assert false : "we have a constraint of the form x in {x, ...}, which is tautological, but "
						+ "SetConstraintConjunction should be normalized";
				return false;
			}

		}

		return true;
	}

	/**
	 * checks if a set of SetConstraints is fully normalized (and possibly more
	 * checks)
	 *
	 * @param constrainedElement
	 * @param filtered
	 * @return
	 */
	public static <ELEM extends ICongruenceClosureElement<ELEM>> boolean sanityCheck(// final ELEM constrainedElement,
			final Set<SetConstraint<ELEM>> filtered) {
		if (filtered == null) {
			return true;
		}

		if (filtered.isEmpty()) {
			// tautological --> normalize to null
			assert false;
			return false;
		}

		return true;
	}

//	public static <ELEM extends ICongruenceClosureElement<ELEM>> Set<SetConstraint<ELEM>> updateOnChangedRepresentative(
//			final Set<SetConstraint<ELEM>> setConstraints, final ELEM oldRep,
//			final ELEM newRep) {
//		final Set<SetConstraint<ELEM>> result = new HashSet<>();
//		for (final SetConstraint<ELEM> setConstraint : setConstraints) {
//			result.add(SetConstraint.updateOnChangedRepresentative(setConstraint, oldRep, newRep));
//		}
//		return result;
//	}
//
//	public static <ELEM extends ICongruenceClosureElement<ELEM>> Set<SetConstraint<ELEM>> updateOnChangedRepresentative(
//			final Set<SetConstraint<ELEM>> setConstraints, final ELEM elem1OldRep, final ELEM elem2OldRep,
//			final ELEM newRep) {
//		final Set<SetConstraint<ELEM>> result = new HashSet<>();
//		boolean madeChanges = false;
//		for (final SetConstraint<ELEM> setConstraint : setConstraints) {
//			final SetConstraint<ELEM> updated =
//					SetConstraint.updateOnChangedRepresentative(setConstraint, elem1OldRep, elem2OldRep, newRep);
//			madeChanges |= updated != setConstraint;
//			result.add(updated);
//		}
//		if (!madeChanges) {
//			return setConstraints;
//		}
//		return result;
//	}
//
//	public static <ELEM extends ICongruenceClosureElement<ELEM>> Set<SetConstraint<ELEM>> transformElements(
//			final Set<SetConstraint<ELEM>> setConstraints, final Function<ELEM, ELEM> elemTransformer) {
//		final Set<SetConstraint<ELEM>> result = new HashSet<>();
//		for (final SetConstraint<ELEM> setConstraint : setConstraints) {
//			result.add(SetConstraint.transformElements(setConstraint, elemTransformer));
//		}
//		return result;
//	}
//
//	public static <ELEM extends ICongruenceClosureElement<ELEM>> Set<SetConstraint<ELEM>> meet(
//			final CCLiteralSetConstraints<ELEM> surroundingConstraint,
//			final Set<SetConstraint<ELEM>> constraintConjunction1,
//			final Set<SetConstraint<ELEM>> constraintConjunction2) {
//		if (SetConstraintConjunction.isTautological(constraintConjunction1)) {
//			return constraintConjunction2;
//		}
//		if (SetConstraintConjunction.isTautological(constraintConjunction2)) {
//			return constraintConjunction1;
//		}
//		if (SetConstraintConjunction.isInconsistent(constraintConjunction1)) {
//			return getInconsistentSetConstraintConjunction();
//		}
//		if (SetConstraintConjunction.isInconsistent(constraintConjunction2)) {
//			return getInconsistentSetConstraintConjunction();
//		}
//
//		final Collection<SetConstraint<ELEM>> newSetConstraints = DataStructureUtils.union(constraintConjunction1,
//				constraintConjunction2);
//
//		return surroundingConstraint.getCongruenceClosure().getManager()
//				.normalizeSetConstraintConjunction(surroundingConstraint, newSetConstraints);
//	}
//
//	/**
//	 * Check if the two constraints would contradict "if they were about the same
//	 * element". (Used in getEqualityStatus..)
//	 *
//	 * assumes (like all methods of this kind) that the SetConstraints are aligned in terms of representatives
//	 *
//	 * @param litConstraint1
//	 * @param litConstraint2
//	 * @return
//	 */
//	public static <ELEM extends ICongruenceClosureElement<ELEM>> boolean meetIsInconsistent(
//			final CCLiteralSetConstraints<ELEM> surroundingConstraint, final Set<SetConstraint<ELEM>> litConstraint1,
//			final Set<SetConstraint<ELEM>> litConstraint2) {
//
//		final Collection<SetConstraint<ELEM>> meet = meet(surroundingConstraint, litConstraint1, litConstraint2);
//		return SetConstraintConjunction.isInconsistent(meet);
//	}
//
//	/**
//	 * Can deal with "null" arguments (which represent the "Top" value).
//	 *
//	 * Basic law for this: A /\ B -> C /\ D <=> A -> C /\ A -> D \/ B -> C /\ B -> D
//	 *
//	 *
//	 * @param constraintConjunction1
//	 * @param constraintConjunction2
//	 * @return
//	 */
//	public static <ELEM extends ICongruenceClosureElement<ELEM>> boolean isStrongerThan(
//			final Set<SetConstraint<ELEM>> constraintConjunction1,
//			final Set<SetConstraint<ELEM>> constraintConjunction2) {
//		if (SetConstraintConjunction.isTautological(constraintConjunction1)) {
//			// cc2 = Top
//			return true;
//		}
//		if (SetConstraintConjunction.isTautological(constraintConjunction2)) {
//			// cc1 = Top, cc2 != Top
//			return false;
//		}
//		if (SetConstraintConjunction.isInconsistent(constraintConjunction1)) {
//			// cc1 = Bot
//			return true;
//		}
//		if (SetConstraintConjunction.isInconsistent(constraintConjunction2)) {
//			// cc2 = Bot, cc1 != Bot
//			return false;
//		}
//
//		for (final SetConstraint<ELEM> lhsConjunct : constraintConjunction1) {
//
//			boolean conjunctionHolds = true;
//			for (final SetConstraint<ELEM> rhsConjunct : constraintConjunction2) {
//				if (!SetConstraint.isStrongerThan(lhsConjunct, rhsConjunct)) {
//					conjunctionHolds = false;
//					break;
//				}
//			}
//
//			if (conjunctionHolds) {
//				return true;
//			}
//		}
//
//		return false;
//	}
//
//	public static <ELEM extends ICongruenceClosureElement<ELEM>> Set<SetConstraint<ELEM>> getInconsistentSetConstraintConjunction() {
//		return Collections.singleton(SetConstraint.getInconsistentSetConstraint());
//	}
//
//	public static <ELEM extends ICongruenceClosureElement<ELEM>> Set<SetConstraint<ELEM>> getTautologicalSetConstraintConjunction() {
//		return Collections.emptySet();
//	}
//
//	public static <ELEM extends ICongruenceClosureElement<ELEM>> Set<SetConstraint<ELEM>> join(
//			final CCLiteralSetConstraints<ELEM> surroundingSetConstraints,
//			final Set<SetConstraint<ELEM>> constraintConjunction1,
//			final Set<SetConstraint<ELEM>> constraintConjunction2) {
//		if (SetConstraintConjunction.isTautological(constraintConjunction1)) {
//			return getTautologicalSetConstraintConjunction();
//		}
//		if (SetConstraintConjunction.isTautological(constraintConjunction2)) {
//			return getTautologicalSetConstraintConjunction();
//		}
//		if (SetConstraintConjunction.isInconsistent(constraintConjunction1)) {
//			return constraintConjunction2;
//		}
//		if (SetConstraintConjunction.isInconsistent(constraintConjunction2)) {
//			return constraintConjunction1;
//		}
//		final Set<SetConstraint<ELEM>> newSetConstraints = new HashSet<>();
//
//		for (final SetConstraint<ELEM> sc1 : constraintConjunction1) {
//			for (final SetConstraint<ELEM> sc2 : constraintConjunction2) {
//				newSetConstraints.add(SetConstraint.join(sc1, sc2));
//			}
//		}
//
//		return newSetConstraints;
//	}
//
//	/**
//	 * assumes that representatives are resolved..
//	 *
//	 * @param constraints
//	 * @return
//	 */
//	public static <ELEM extends ICongruenceClosureElement<ELEM>> boolean isTautological(
//			final Set<SetConstraint<ELEM>> constraints) {
//		if (constraints == null) {
//			return true;
//		}
//		if (constraints.isEmpty()) {
//			return true;
//		}
//		return false;
//	}
//
//	public static <ELEM extends ICongruenceClosureElement<ELEM>> boolean isInconsistent(
//			final Collection<SetConstraint<ELEM>> constraints) {
//		if (constraints == null) {
//			return false;
//		}
//		return constraints.stream().anyMatch(sc -> sc.isInconsistent());
//	}
//
//	public static <ELEM extends ICongruenceClosureElement<ELEM>> Set<ELEM> getSingletonValues(
//			final Set<SetConstraint<ELEM>> constraints) {
//		return constraints.stream().filter(sc -> sc.isSingleton())
//				.map(sc -> sc.getSingletonValue())
//				.collect(Collectors.toSet());
//	}
//
//	public static <ELEM extends ICongruenceClosureElement<ELEM>> Set<SetConstraint<ELEM>> filterWithDisequalities(
//			final CongruenceClosure<ELEM> congruenceClosure, final ELEM constrainedElement,
//			final Set<SetConstraint<ELEM>> constraints) {
//		final Set<SetConstraint<ELEM>> result = new HashSet<>();
//		boolean madeChanges = false;
//		for (final SetConstraint<ELEM> setConstraint : constraints) {
//			final SetConstraint<ELEM> filtered = SetConstraint.filterWithDisequalities(setConstraint,
//					constrainedElement, congruenceClosure);
//			madeChanges |= filtered != setConstraint;
//			result.add(filtered);
//		}
//		if (!madeChanges) {
//			return constraints;
//		}
//		return result;
//	}
//
//	public Set<SetConstraint<ELEM>> getSetConstraints() {
//		return Collections.unmodifiableSet(mSetConstraints);
//	}
//
//	public static <ELEM extends ICongruenceClosureElement<ELEM>> boolean isTautological(
//			final SetConstraintConjunction<ELEM> newConstraint) {
//		if (newConstraint == null) {
//			return true;
//		}
//		if (newConstraint.isTautological()) {
//			return true;
//		}
//		return false;
//	}
//
//	public static <ELEM extends ICongruenceClosureElement<ELEM>> Set<SetConstraint<ELEM>>
//			filterWithDisequality(final Set<SetConstraint<ELEM>> setConstraints, final ELEM elem) {
//		final Set<SetConstraint<ELEM>> result = new HashSet<>();
//		boolean madeChanges = false;
//		for (final SetConstraint<ELEM> sc : setConstraints) {
//			final SetConstraint<ELEM> filtered = SetConstraint.filterWithDisequality(sc, elem);
//			madeChanges |= filtered != sc;
//			result.add(filtered);
//		}
//		if (!madeChanges) {
//			return setConstraints;
//		}
//		return result;
//	}
//
//	public static <ELEM extends ICongruenceClosureElement<ELEM>> Set<SetConstraint<ELEM>>
//			updateOnChangedRepresentative(final Set<SetConstraint<ELEM>> oldConstraint,
//					final CongruenceClosure<ELEM> newCc) {
//		if (oldConstraint == null) {
//			return null;
//		}
//
//		final Set<SetConstraint<ELEM>> result = new HashSet<>();
//		boolean madeChanges = false;
//		for (final SetConstraint<ELEM> sc : oldConstraint) {
//			final SetConstraint<ELEM> updRep = SetConstraint.updateOnChangedRepresentative(sc, newCc);
//			madeChanges |= updRep != sc;
//			result.add(updRep);
//		}
//
//		if (!madeChanges) {
//			// TODO extra wrapping is not nice
//			return oldConstraint;
//		}
//		return result;
//	}

}

/**
 * note that this is sublty different from the CongruenceClosureComparator,
 * because here we want to keep the strongest, not the weakest elements when
 * filtering..
 *
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ELEM>
 */
class SetConstraintComparator<ELEM extends ICongruenceClosureElement<ELEM>>
		implements IPartialComparator<SetConstraint<ELEM>> {

	private final SetConstraintManager<ELEM> mSetConstraintManager;
	public SetConstraintComparator(final SetConstraintManager<ELEM> setConstraintManager) {
		mSetConstraintManager = setConstraintManager;
	}

	@Override
	public ComparisonResult compare(final SetConstraint<ELEM> o1, final SetConstraint<ELEM> o2) {
		if (o1.equals(o2)) {
			return ComparisonResult.EQUAL;
		}
		final boolean o1Stronger = mSetConstraintManager.isStrongerThan(o1, o2);
		final boolean o2Stronger = mSetConstraintManager.isStrongerThan(o2, o1);
		if (o1Stronger && o2Stronger) {
			return ComparisonResult.EQUAL;
		} else if (o1Stronger) {
			// return ComparisonResult.STRICTLY_SMALLER;
			return ComparisonResult.STRICTLY_GREATER;
		} else if (o2Stronger) {
			return ComparisonResult.STRICTLY_SMALLER;
			// return ComparisonResult.STRICTLY_GREATER;
		} else {
			return ComparisonResult.INCOMPARABLE;
		}
	}
}
