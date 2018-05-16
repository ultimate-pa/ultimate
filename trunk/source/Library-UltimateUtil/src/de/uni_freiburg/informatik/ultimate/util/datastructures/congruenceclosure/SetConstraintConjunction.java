package de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PartialOrderCache;

/**
 * Represents a conjunction over single set constraints that all constrain the same element.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ELEM>
 */
public class SetConstraintConjunction<ELEM extends ICongruenceClosureElement<ELEM>> {

	private final ELEM mConstrainedElement;


	CCLiteralSetConstraints<ELEM> mSurroundingCCSetConstraints;

	Set<SetConstraint<ELEM>> mSetConstraints;


	private boolean mIsInconsistent;


	private SetConstraintConjunction(final CCLiteralSetConstraints<ELEM> surroundingSetConstraints,
			final ELEM constrainedElement,
			final Collection<SetConstraint<ELEM>> setConstraints) {
		mConstrainedElement = constrainedElement;
		mSurroundingCCSetConstraints = surroundingSetConstraints;
		mSetConstraints = new HashSet<>();
	}

	public SetConstraintConjunction(final CCLiteralSetConstraints<ELEM> surroundingSetConstraints,
			final ELEM constrainedElement,
			final Set<ELEM> elements) {
		mConstrainedElement = constrainedElement;
		mSurroundingCCSetConstraints = surroundingSetConstraints;
		mSetConstraints = new HashSet<>();
		mSetConstraints.add(new SetConstraint<>(this, elements));
	}

	/**
	 * copy constructor
	 *
	 * @param original
	 */
	public SetConstraintConjunction(final SetConstraintConjunction<ELEM> original) {
		mConstrainedElement = original.mConstrainedElement;
	}

	/**
	 * The given element is projected away. Assume it is not mConstrainedElement. Project it in the sets.
	 *
	 * @param elem
	 */
	public void projectAway(final ELEM elem) {
		assert mSurroundingCCSetConstraints.getCongruenceClosure().isRepresentative(elem) : "right?..";
		assert !elem.equals(mConstrainedElement);

		/*
		 * remove constraints that have elem on their right hand side
		 * (a more precise alternative would be to introduce a dummy element, effectively an existentially quantified
		 *  variable.. but we would have to introduce one for every projected element, right?..)
		 */
		for (final SetConstraint<ELEM> sc : new HashSet<>(mSetConstraints)) {
			if (sc.containsElement(elem)) {
				mSetConstraints.remove(sc);
			}
		}

	}

	/**
	 * Propagate according to the disequality "mConstrainedElement != elem".
	 *
	 * rule: e in L /\ e != l --> e in L\{l}
	 *
	 * @param elem1Rep
	 */
	public void filterWithDisequality(final ELEM elem) {
		for (final SetConstraint<ELEM> sc : mSetConstraints) {
			sc.filterWithDisequality(elem);
		}
	}

	public ELEM getSingletonValue() {
		assert isSingleton() : "check for isSingleton before calling this";
		return mSetConstraints.iterator().next().getElementSet().iterator().next();
	}

	public boolean isSingleton() {
		final boolean result = mSetConstraints.stream().allMatch(sc -> sc.getElementSet().size() == 1);
		assert mSetConstraints.size() == 1 : "not cleaned up??";
		return result;
	}

	public boolean isInconsistent() {
		return mIsInconsistent;
	}

	public CongruenceClosure<ELEM> getCongruenceClosure() {
		return mSurroundingCCSetConstraints.getCongruenceClosure();
	}

	public ELEM getConstrainedElement() {
		assert mConstrainedElement != null;
		return mConstrainedElement;
	}

	/**
	 * Apply propagation rule
	 *  e in L /\ e != l --> e in L\{l}
	 */
	public void filterWithDisequalities(final CongruenceClosure<ELEM> congruenceClosure) {
		for (final SetConstraint<ELEM> setConstraint : mSetConstraints) {
			setConstraint.filterWithDisequalities();
		}
	}

	public void updateOnChangedRepresentative(final ELEM oldRep, final ELEM newRep) {
		for (final SetConstraint<ELEM> setConstraint : mSetConstraints) {
			setConstraint.updateOnChangedRepresentative(oldRep, newRep);
		}
	}

	public void updateOnChangedRepresentative(final ELEM elem1OldRep, final ELEM elem2OldRep, final ELEM newRep) {
		for (final SetConstraint<ELEM> setConstraint : mSetConstraints) {
			setConstraint.updateOnChangedRepresentative(elem1OldRep, elem2OldRep, newRep);
		}
	}

//	public static <ELEM extends ICongruenceClosureElement<ELEM>> SetConstraintConjunction<ELEM> transformElements(
	//				final SetConstraintConjunction<ELEM> value,
	public void transformElements(final Function<ELEM, ELEM> elemTransformer) {
		for (final SetConstraint<ELEM> setConstraint : mSetConstraints) {
			setConstraint.transformElements(elemTransformer);
		}
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> SetConstraintConjunction<ELEM>
		buildSetConstraintConjunction(final CCLiteralSetConstraints<ELEM> surroundingSetConstraints,
			final ELEM constrainedElement,
			final Collection<SetConstraint<ELEM>> setConstraints) {

		//TODO: only instantiate SetConstraintComparator once??

		final PartialOrderCache<SetConstraint<ELEM>> poc = new PartialOrderCache<>(new SetConstraintComparator<>());
		final Set<SetConstraint<ELEM>> filtered = poc.getMaximalRepresentatives(setConstraints);

		return new SetConstraintConjunction<>(surroundingSetConstraints, constrainedElement, filtered);
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> SetConstraintConjunction<ELEM> meet(
			final SetConstraintConjunction<ELEM> constraintConjunction1,
			final SetConstraintConjunction<ELEM> constraintConjunction2) {
		if (constraintConjunction1 == null) {
			return constraintConjunction2;
		}
		if (constraintConjunction2 == null) {
			return constraintConjunction1;
		}
		if (constraintConjunction1.isInconsistent()) {
			return constraintConjunction1;
		}
		if (constraintConjunction2.isInconsistent()) {
			return constraintConjunction2;
		}

		assert constraintConjunction1.mSurroundingCCSetConstraints
			== constraintConjunction2.mSurroundingCCSetConstraints;
		final CCLiteralSetConstraints<ELEM> surroundingConstraint = constraintConjunction1.mSurroundingCCSetConstraints;
		assert constraintConjunction1.mConstrainedElement == constraintConjunction2.mConstrainedElement;
		final ELEM constrainedElement = constraintConjunction1.mConstrainedElement;
		final Collection<SetConstraint<ELEM>> newSetConstraints =
				DataStructureUtils.union(constraintConjunction1.mSetConstraints,
						constraintConjunction2.mSetConstraints);

		return buildSetConstraintConjunction(surroundingConstraint, constrainedElement, newSetConstraints);
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> boolean meetIsInconsistent(
			final SetConstraintConjunction<ELEM> litConstraint1,
			final SetConstraintConjunction<ELEM> litConstraint2) {
		return meet(litConstraint1, litConstraint2).isInconsistent();
	}

	/**
	 * Can deal with "null" arguments (which represent the "Top" value).
	 *
	 * Basic law for this:
	 *   A /\ B -> C /\ D
	 *  <=>
	 *     A -> C /\ A -> D
	 *  \/ B -> C /\ B -> D
	 *
	 *
	 * @param constraintConjunction1
	 * @param constraintConjunction2
	 * @return
	 */
	public static <ELEM extends ICongruenceClosureElement<ELEM>> boolean isStrongerThan(
			final SetConstraintConjunction<ELEM> constraintConjunction1,
			final SetConstraintConjunction<ELEM> constraintConjunction2) {
		assert constraintConjunction1.mConstrainedElement == constraintConjunction2.mConstrainedElement;
		if (constraintConjunction2 == null) {
			// cc2 = Top
			return true;
		}
		if (constraintConjunction1 == null) {
			// cc1 = Top, cc2 != Top
			return false;
		}
		if (constraintConjunction1.isInconsistent()) {
			// cc1 = Bot
			return true;
		}
		if (constraintConjunction2.isInconsistent()) {
			// cc2 = Bot, cc1 != Bot
			return false;
		}

		assert constraintConjunction1.mSetConstraints.size() > 0;
		assert constraintConjunction2.mSetConstraints.size() > 0;

		for (final SetConstraint<ELEM> lhsConjunct : constraintConjunction1.mSetConstraints) {

			boolean conjunctionHolds = true;
			for (final SetConstraint<ELEM> rhsConjunct : constraintConjunction2.mSetConstraints) {
				if (!SetConstraint.isStrongerThan(lhsConjunct, rhsConjunct)) {
					conjunctionHolds = false;
					break;
				}
			}

			if (conjunctionHolds) {
				return true;
			}
		}

		return false;
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> SetConstraintConjunction<ELEM> join(
			final SetConstraintConjunction<ELEM> constraintConjunction1,
			final SetConstraintConjunction<ELEM> constraintConjunction2) {
		if (constraintConjunction1 == null) {
			return constraintConjunction2;
		}
		if (constraintConjunction2 == null) {
			return constraintConjunction1;
		}
		if (constraintConjunction1.isInconsistent()) {
			return constraintConjunction1;
		}
		if (constraintConjunction2.isInconsistent()) {
			return constraintConjunction2;
		}

		assert constraintConjunction1.mSurroundingCCSetConstraints
			== constraintConjunction2.mSurroundingCCSetConstraints;
		final CCLiteralSetConstraints<ELEM> surroundingConstraint = constraintConjunction1.mSurroundingCCSetConstraints;

		assert constraintConjunction1.mConstrainedElement == constraintConjunction2.mConstrainedElement;
		final ELEM constrainedElement = constraintConjunction1.mConstrainedElement;

		final Collection<SetConstraint<ELEM>> newSetConstraints = new HashSet<>();

		for (final SetConstraint<ELEM> sc1 : constraintConjunction1.mSetConstraints) {
			for (final SetConstraint<ELEM> sc2 : constraintConjunction1.mSetConstraints) {
				newSetConstraints.add(SetConstraint.join(sc1, sc2));
			}
		}

		return buildSetConstraintConjunction(surroundingConstraint, constrainedElement, newSetConstraints);
	}

	public boolean sanityCheck() {
		for (final SetConstraint<ELEM> conjunct : mSetConstraints) {
			if (!conjunct.sanityCheck()) {
				assert false;
				return false;
			}
		}

		if (mSurroundingCCSetConstraints.getConstraint(mConstrainedElement) != this) {
				assert false;
				return false;
		}

		return true;
	}

	public Set<Set<ELEM>> getElementSets() {
		final Set<Set<ELEM>> result = new HashSet<>();

		for (final SetConstraint<ELEM> sc : mSetConstraints) {
			result.add(sc.getElementSet());
		}

		return Collections.unmodifiableSet(result);
	}
}

/**
 *
 * Represents a conjunction over single set constraints of the form e in L cup N, where L is a set of literals and N is
 * a set of non-literal elements.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ELEM>
 */
class SetConstraint<ELEM extends ICongruenceClosureElement<ELEM>> {

	/**
	 * the conjunction this constraint belongs to
	 */
	private final SetConstraintConjunction<ELEM> mSurroundingScConjunction;

	private final Set<ELEM> mLiterals;
	private final Set<ELEM> mNonLiterals;

	public SetConstraint(final SetConstraintConjunction<ELEM> surroundingSetCc, final Set<ELEM> unsortedElements) {
		this(surroundingSetCc,
				unsortedElements.stream().filter(ELEM::isLiteral).collect(Collectors.toSet()),
				unsortedElements.stream().filter(e -> !e.isLiteral()).collect(Collectors.toSet()));
//		mSurroundingScConjunction = surroundingSetCc;
//		mLiterals = new HashSet<>();
//		mNonLiterals = new HashSet<>();
//		for (final ELEM e : unsortedElements) {
//			if (e.isLiteral()) {
//				mLiterals.add(e);
//			} else {
//				mNonLiterals.add(e);
//			}
//		}
	}

	private SetConstraint(final SetConstraintConjunction<ELEM> surroundingSetCc, final Set<ELEM> literals,
			final Set<ELEM> nonLiterals) {
		mSurroundingScConjunction = surroundingSetCc;
		mLiterals = new HashSet<>(literals);
		mNonLiterals = new HashSet<>(nonLiterals);
		assert sanityCheck();
	}

	public void transformElements(final Function<ELEM, ELEM> elemTransformer) {
		for (final ELEM l : new HashSet<>(mLiterals)) {
			if (mLiterals.remove(l)) {
				mLiterals.add(elemTransformer.apply(l));
			}
		}
		for (final ELEM l : new HashSet<>(mNonLiterals)) {
			if (mNonLiterals.remove(l)) {
				mNonLiterals.add(elemTransformer.apply(l));
			}
		}
		assert sanityCheck();
	}

	public void updateOnChangedRepresentative(final ELEM elem1OldRep, final ELEM elem2OldRep, final ELEM newRep) {
		if (elem1OldRep.isLiteral()) {
			mLiterals.remove(elem1OldRep);
		} else {
			mNonLiterals.remove(elem1OldRep);
		}
		if (elem2OldRep.isLiteral()) {
			mLiterals.remove(elem2OldRep);
		} else {
			mNonLiterals.remove(elem2OldRep);
		}
		if (newRep.isLiteral()) {
			mLiterals.add(newRep);
		} else {
			mNonLiterals.add(newRep);
		}
	}

	public void updateOnChangedRepresentative(final ELEM oldRep, final ELEM newRep) {
		if (oldRep.isLiteral()) {
			mLiterals.remove(oldRep);
		} else {
			mNonLiterals.remove(oldRep);
		}
		if (newRep.isLiteral()) {
			mLiterals.add(newRep);
		} else {
			mNonLiterals.add(newRep);
		}
	}

	public Set<ELEM> getElementSet() {
		return DataStructureUtils.union(mLiterals, mNonLiterals);
	}

	public void filterWithDisequality(final ELEM elem) {
		assert mSurroundingScConjunction.getCongruenceClosure().isRepresentative(elem);
		mLiterals.remove(elem);
		mNonLiterals.remove(elem);
	}

	public boolean containsElement(final ELEM elem) {
		if (elem.isLiteral()) {
			return mLiterals != null && mLiterals.contains(elem);
		} else {
			return mNonLiterals != null && mNonLiterals.contains(elem);
		}
	}

	/**
	 * Apply propagation rule
	 *  e in L /\ e != l --> e in L\{l}
	 */
	public void filterWithDisequalities() {

		final CongruenceClosure<ELEM> congruenceClosure = mSurroundingScConjunction.getCongruenceClosure();
		final ELEM constrainedElement = mSurroundingScConjunction.getConstrainedElement();


		{
			final Set<ELEM> newLiterals = new HashSet<>(mLiterals);

			for (final ELEM lit : mLiterals) {
				/*
				 * rule: e in L /\ e != l --> e in L\{l}
				 */
				if (congruenceClosure.getEqualityStatus(constrainedElement, lit) == EqualityStatus.NOT_EQUAL) {
					newLiterals.remove(lit);
				}
			}
			mLiterals.clear();
			mLiterals.addAll(newLiterals);
		}

		{
			final Set<ELEM> newNonLiterals = new HashSet<>(mNonLiterals);

			for (final ELEM lit : mNonLiterals) {
				/*
				 * rule: e in L /\ e != l --> e in L\{l}
				 */
				if (congruenceClosure.getEqualityStatus(constrainedElement, lit) == EqualityStatus.NOT_EQUAL) {
					newNonLiterals.remove(lit);
				}
			}
			mNonLiterals.clear();
			mNonLiterals.addAll(newNonLiterals);
		}
	}


	public static <ELEM extends ICongruenceClosureElement<ELEM>> boolean isStrongerThan(
			final SetConstraint<ELEM> lhsConjunct, final SetConstraint<ELEM> rhsConjunct) {
		if (!rhsConjunct.mLiterals.containsAll(lhsConjunct.mLiterals)) {
			return false;
		}
		if (!rhsConjunct.mNonLiterals.containsAll(lhsConjunct.mNonLiterals)) {
			return false;
		}
		return true;
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> SetConstraint<ELEM> join(
			final SetConstraint<ELEM> sc1, final SetConstraint<ELEM> sc2) {
		assert sc1.mSurroundingScConjunction == sc2.mSurroundingScConjunction;
		return new SetConstraint<>(sc1.mSurroundingScConjunction,
				DataStructureUtils.union(sc1.mLiterals, sc2.mLiterals),
				DataStructureUtils.union(sc1.mNonLiterals, sc2.mNonLiterals));
	}

	public boolean sanityCheck() {
		if (mLiterals.size() == 1 && mNonLiterals.isEmpty()) {
			// we leave constraints of the form l in {l} implicit
			assert false;
			return false;
		}
		if (!mLiterals.stream().allMatch(ELEM::isLiteral)) {
			assert false;
			return false;
		}

		if (mNonLiterals.stream().anyMatch(ELEM::isLiteral)) {
			assert false;
			return false;
		}

		return true;
	}
}

/**
 * note that this is sublty different from the CongruenceClosureComparator, because here we want to keep the strongest,
 * not the weakest elements when filtering..
 *
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ELEM>
 */
class SetConstraintComparator<ELEM extends ICongruenceClosureElement<ELEM>>
	implements IPartialComparator<SetConstraint<ELEM>> {

	@Override
	public ComparisonResult compare(final SetConstraint<ELEM> o1, final SetConstraint<ELEM> o2) {
		if (o1.equals(o2)) {
			return ComparisonResult.EQUAL;
		}
		final boolean o1Stronger = SetConstraint.isStrongerThan(o1, o2);
		final boolean o2Stronger = SetConstraint.isStrongerThan(o2, o1);
		if (o1Stronger && o2Stronger) {
			return ComparisonResult.EQUAL;
		} else if (o1Stronger) {
//			return ComparisonResult.STRICTLY_SMALLER;
			return ComparisonResult.STRICTLY_GREATER;
		} else if (o2Stronger) {
			return ComparisonResult.STRICTLY_SMALLER;
//			return ComparisonResult.STRICTLY_GREATER;
		} else {
			return ComparisonResult.INCOMPARABLE;
		}
	}
}
