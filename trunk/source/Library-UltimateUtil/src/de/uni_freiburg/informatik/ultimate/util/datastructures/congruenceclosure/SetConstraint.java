package de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;

/**
 *
 * Represents a conjunction over single set constraints of the form e in L cup N, where L is a set of literals and N is
 * a set of non-literal elements.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ELEM>
 */
public class SetConstraint<ELEM extends ICongruenceClosureElement<ELEM>> {

	/**
	 * the conjunction this constraint belongs to
	 */
//	private final SetConstraintConjunction<ELEM> mSurroundingScConjunction;

	private final Set<ELEM> mLiterals;
	private final Set<ELEM> mNonLiterals;

	/**
	 * sufficient condition, not necessary for being inconsistent
	 */
	private final boolean mIsInconsistent;


	protected SetConstraint(final boolean inconsistent) {
		assert inconsistent : "use other constructor for this case!";
//		mSurroundingScConjunction = null;
		mLiterals = null;
		mNonLiterals = null;
		mIsInconsistent = true;
//		assert sanityCheck();
	}

	public boolean isSingleton() {
		return getElementSet().size() == 1;
	}

	public ELEM getSingletonValue() {
		assert isSingleton();
		return getElementSet().iterator().next();
	}

	/**
	 * Construct a SetConstraint that has not yet been added to a SetConstraintConjunction.
	 *
	 * @param literals
	 * @param nonLiterals
	 */
	protected SetConstraint(//final SetConstraintConjunction<ELEM> surroundingSetCc,
			final Set<ELEM> literals,
			final Set<ELEM> nonLiterals) {
		assert literals.stream().allMatch(ELEM::isLiteral);
		assert !nonLiterals.stream().anyMatch(ELEM::isLiteral);

//		mSurroundingScConjunction = null;
		mLiterals = Collections.unmodifiableSet(literals);
		mNonLiterals = Collections.unmodifiableSet(nonLiterals);

//		mLiterals = literals;
//		mNonLiterals = nonLiterals;
		mIsInconsistent = literals.isEmpty() && nonLiterals.isEmpty();
		assert !mIsInconsistent : "use other constructor, no?";
		assert sanityCheck();
	}

//	/**
//	 * copy constructor that may change surrounding set constraints
//	 *
//	 * @param surroundingSetCc
//	 * @param sc
//	 */
//	SetConstraint(final SetConstraintConjunction<ELEM> surroundingSetCc, final SetConstraint<ELEM> sc) {
//		mSurroundingScConjunction = surroundingSetCc;
//		mLiterals = new HashSet<>(sc.mLiterals);
//		mNonLiterals = new HashSet<>(sc.mNonLiterals);
//		mIsInconsistent = false;
//		assert sanityCheck();
//	}

	public Set<ELEM> getLiterals() {
//		assert hasOnlyLiterals();
		return Collections.unmodifiableSet(mLiterals);
	}

	/**
	 *
	 * @param elemRep
	 * @param literals
	 * @return true if made changes
	 */
	public boolean expandVariableToLiterals(final ELEM elemRep, final Set<ELEM> literals) {
		if (mNonLiterals.contains(elemRep)) {
			mNonLiterals.remove(elemRep);
			mLiterals.addAll(literals);
			return true;
		}
		return false;
	}

	public boolean hasOnlyLiterals() {
		return mNonLiterals.isEmpty();
	}

	public boolean isInconsistent() {
		return mIsInconsistent || (mLiterals.isEmpty() && mNonLiterals.isEmpty());
	}

//	public void updateOnChangedRepresentative(final ELEM elem1OldRep, final ELEM elem2OldRep, final ELEM newRep) {
	public static <ELEM extends ICongruenceClosureElement<ELEM>> SetConstraint<ELEM>
				updateOnChangedRepresentative(final SetConstraint<ELEM> oldSetConstraint,
			final ELEM elem1OldRep, final ELEM elem2OldRep, final ELEM newRep) {

		final Set<ELEM> oldElements = oldSetConstraint.getElementSet();
		if (!oldElements.contains(elem1OldRep) && !oldElements.contains(elem2OldRep)) {
			return oldSetConstraint;
		}

		final Set<ELEM> newLiterals = new HashSet<>(oldSetConstraint.mLiterals);
		final Set<ELEM> newNonLiterals = new HashSet<>(oldSetConstraint.mNonLiterals);

		if (elem1OldRep.isLiteral()) {
			newLiterals.remove(elem1OldRep);
		} else {
			newNonLiterals.remove(elem1OldRep);
		}
		if (elem2OldRep.isLiteral()) {
			newLiterals.remove(elem2OldRep);
		} else {
			newNonLiterals.remove(elem2OldRep);
		}

		if (newRep.isLiteral()) {
			newLiterals.add(newRep);
		} else {
			newNonLiterals.add(newRep);
		}
		return buildSetConstraint(newLiterals, newNonLiterals);
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> SetConstraint<ELEM>
	 		updateOnChangedRepresentative(final SetConstraint<ELEM> oldSetConstraint, final ELEM oldRep, final ELEM newRep) {

		final Set<ELEM> oldElements = oldSetConstraint.getElementSet();
		if (!oldElements.contains(oldRep)) {
			return oldSetConstraint;
		}

		final Set<ELEM> newLiterals = new HashSet<>(oldSetConstraint.mLiterals);
		final Set<ELEM> newNonLiterals = new HashSet<>(oldSetConstraint.mNonLiterals);

		if (oldRep.isLiteral()) {
			newLiterals.remove(oldRep);
		} else {
			newNonLiterals.remove(oldRep);
		}

		if (newRep.isLiteral()) {
			newLiterals.add(newRep);
		} else {
			newNonLiterals.add(newRep);
		}
		return buildSetConstraint(newLiterals, newNonLiterals);
	}

	/**
	 * all elements on the right hand side of this constraint (literals and non-literals)
	 * @return
	 */
	public Set<ELEM> getElementSet() {
		return DataStructureUtils.union(mLiterals, mNonLiterals);
	}

//	public void filterWithDisequality(final ELEM elem) {
//		assert mSurroundingScConjunction.getCongruenceClosure().isRepresentative(elem);
//		mLiterals.remove(elem);
//		mNonLiterals.remove(elem);
//	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> SetConstraint<ELEM>
			filterWithDisequality(final SetConstraint<ELEM> constraint, final ELEM elem) {
//		assert mSurroundingScConjunction.getCongruenceClosure().isRepresentative(elem);
//		mLiterals.remove(elem);
//		mNonLiterals.remove(elem);

		if (!constraint.mLiterals.contains(elem) && !constraint.mNonLiterals.contains(elem)) {
			return constraint;
		}

		final Set<ELEM> newLiterals = new HashSet<>(constraint.mLiterals);
		final Set<ELEM> newNonLiterals = new HashSet<>(constraint.mNonLiterals);
		newLiterals.remove(elem);
		newNonLiterals.remove(elem);
		return buildSetConstraint(newLiterals, newNonLiterals);
	}


	public static <ELEM extends ICongruenceClosureElement<ELEM>> SetConstraint<ELEM>
			transformElements(final SetConstraint<ELEM> constraint, final Function<ELEM, ELEM> elemTransformer) {
		//	public void transformElements(final Function<ELEM, ELEM> elemTransformer) {
//		for (final ELEM l : new HashSet<>(mLiterals)) {
		final Set<ELEM> newLiterals = new HashSet<>();
		final Set<ELEM> newNonLiterals = new HashSet<>();
		for (final ELEM e : constraint.getElementSet()) {
			final ELEM transformed = elemTransformer.apply(e);
			if (transformed.isLiteral()) {
				newLiterals.add(transformed);
			} else {
				newNonLiterals.add(transformed);
			}
		}
//		for (final ELEM l : constraint.mLiterals) {
////			if (mLiterals.remove(l)) {
////				mLiterals.add(elemTransformer.apply(l));
////			}
//			newLiterals.add(elemTransformer.apply(l));
//		}
////		for (final ELEM l : new HashSet<>(mNonLiterals)) {
//		for (final ELEM l : constraint.mNonLiterals) {
////			if (mNonLiterals.remove(l)) {
////				mNonLiterals.add(elemTransformer.apply(l));
////			}
//			newNonLiterals.add(elemTransformer.apply(l));
//		}
//		assert sanityCheck();
		return buildSetConstraint(newLiterals, newNonLiterals);
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
	 *
	 * Work inplace except if constraint becomes inconsistent or a singleton
	 */
	public static <ELEM extends ICongruenceClosureElement<ELEM>> SetConstraint<ELEM>
			filterWithDisequalities(final SetConstraint<ELEM> oldConstraint, final ELEM constrainedElement,
					final CongruenceClosure<ELEM> congruenceClosure) {

		boolean madeChanges = false;

		final Set<ELEM> newLiterals = new HashSet<>(oldConstraint.mLiterals);
		{

			for (final ELEM lit : oldConstraint.mLiterals) {
				/*
				 * rule: e in L /\ e != l --> e in L\{l}
				 */
				if (congruenceClosure.getEqualityStatus(constrainedElement, lit) == EqualityStatus.NOT_EQUAL) {
					madeChanges |= newLiterals.remove(lit);
				}
			}
		}
		final Set<ELEM> newNonLiterals = new HashSet<>(oldConstraint.mNonLiterals);
		{

			for (final ELEM lit : oldConstraint.mNonLiterals) {
				/*
				 * rule: e in L /\ e != l --> e in L\{l}
				 */
				if (congruenceClosure.getEqualityStatus(constrainedElement, lit) == EqualityStatus.NOT_EQUAL) {
					madeChanges |= newNonLiterals.remove(lit);
				}
			}
		}

		if (!madeChanges) {
			return oldConstraint;
		}

		return SetConstraint.buildSetConstraint(newLiterals, newNonLiterals);
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


	/**
	 * note this constructs "some" meet over the input constraints
	 *
	 * the one that is strongest on literals and weakest on non-literals
	 *
	 * @param scs
	 * @return
	 */
	public static <ELEM extends ICongruenceClosureElement<ELEM>> SetConstraint<ELEM> meet(
			final CCLiteralSetConstraints<ELEM> surroundingSetConstraints,
			final Collection<SetConstraint<ELEM>> scs) {
		if (scs.isEmpty()) {
			// empty meet --> "Top" constraint --> represented by "null"
			return null;
		}

		final Iterator<SetConstraint<ELEM>> scIt = scs.iterator();

		final SetConstraint<ELEM> firstSc = scIt.next();

		Set<ELEM> literals = new HashSet<>(firstSc.mLiterals);
		final Set<ELEM> nonLiterals = new HashSet<>(firstSc.mNonLiterals);

		while (scIt.hasNext()) {
			final SetConstraint<ELEM> current = scIt.next();

			// TODO: is this a good implementation of intersection??
			final Set<ELEM> newLiterals = new HashSet<>();
			for (final ELEM l : literals) {
				if (current.mLiterals.contains(l)) {
					newLiterals.add(l);
				}
			}
			literals = newLiterals;


			nonLiterals.addAll(current.mNonLiterals);
		}

//		final SetConstraintConjunction<ELEM> surroundingSetCc = firstSc.mSurroundingScConjunction;
//		final CCLiteralSetConstraints<ELEM> surroundingSetCc =
//				firstSc.mSurroundingScConjunction.mSurroundingCCSetConstraints;
		return SetConstraint.buildSetConstraint(//surroundingSetConstraints,
				literals, nonLiterals);
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> SetConstraint<ELEM> buildSetConstraint(
//			final CCLiteralSetConstraints<ELEM> surroundingSetConstraints,
//			final SetConstraintConjunction<ELEM> surroundingSetCc,
			final Set<ELEM> literalsRaw,
			final Set<ELEM> nonLiteralsRaw) {
		assert literalsRaw.stream().allMatch(ELEM::isLiteral);
		assert !nonLiteralsRaw.stream().anyMatch(ELEM::isLiteral);

		if (literalsRaw.size() == 1 && nonLiteralsRaw.isEmpty()) {
			return new SingletonSetConstraint<>(literalsRaw.iterator().next());
		}


		final Set<ELEM> literals = new HashSet<>(literalsRaw);
		final Set<ELEM> nonLiterals = new HashSet<>(nonLiteralsRaw);

		// cannot expand here, as surrounding cc might not yet be ready (e.g. during join, meet)
////		final CongruenceClosure<ELEM> cc = surroundingSetCc.getCongruenceClosure();
//		final CongruenceClosure<ELEM> cc = surroundingSetConstraints.getCongruenceClosure();
//
//		// attempt to expand non-literals to literals according to constraints in the surrounding Cc
//		for (final ELEM nl : nonLiteralsRaw) {
//			assert cc.isRepresentative(nl);
//			final SetConstraintConjunction<ELEM> contCons = cc.getContainsConstraintForElement(nl);
//			if (contCons != null && contCons.hasOnlyLiterals()) {
//				nonLiterals.remove(nl);
//				literals.addAll(contCons.getLiterals());
//			}
//		}

		if (literals.isEmpty() && nonLiterals.isEmpty()) {
			return getInconsistentSetConstraint();
		}

		return new SetConstraint<>(literals, nonLiterals);
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> SetConstraint<ELEM> buildSetConstraint(
//			final CCLiteralSetConstraints<ELEM> surroundingSetConstraints,
//			final SetConstraintConjunction<ELEM> surroundingSetCc,
			final Collection<ELEM> unsortedElements) {
		return buildSetConstraint(//surroundingSetConstraints,
				unsortedElements.stream().filter(ELEM::isLiteral).collect(Collectors.toSet()),
				unsortedElements.stream().filter(e -> !e.isLiteral()).collect(Collectors.toSet()));
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> SetConstraint<ELEM> join(
			final SetConstraint<ELEM> sc1, final SetConstraint<ELEM> sc2) {
//		assert sc1.mSurroundingScConjunction == sc2.mSurroundingScConjunction;
		return buildSetConstraint(//sc1.mSurroundingScConjunction.mSurroundingCCSetConstraints,
				DataStructureUtils.union(sc1.mLiterals, sc2.mLiterals),
				DataStructureUtils.union(sc1.mNonLiterals, sc2.mNonLiterals));
	}

	@Override
	public String toString() {
		return "SetConstraint " + mLiterals + " U " + mNonLiterals + "";
	}

	public boolean sanityCheck() {
//		if (!(this instanceof SingletonSetConstraint) && mLiterals.size() == 1 && mNonLiterals.isEmpty()) {
//			// we leave constraints of the form l in {l} implicit
//			assert false;
//			return false;
//		}
		// all elements of mLiterals must be literals
		if (!mLiterals.stream().allMatch(ELEM::isLiteral)) {
			assert false;
			return false;
		}

		// all elements of mNonLiterals must not be literals
		if (mNonLiterals.stream().anyMatch(ELEM::isLiteral)) {
			assert false;
			return false;
		}

		// all elements must have the same sort
		{
			if (getElementSet().size() >= 2) {
				final Iterator<ELEM> it = getElementSet().iterator();
				ELEM currentOne = null;
				ELEM currentTwo = it.next();

				while (it.hasNext()) {
					currentOne = currentTwo;
					currentTwo = it.next();

					if (!currentOne.hasSameTypeAs(currentTwo)) {
						assert false;
						return false;
					}
				}
			}
		}
		return true;
	}

	public boolean sanityCheck(final SetConstraintConjunction<ELEM> surroundingScConjunction) {

		if (!sanityCheck()) {
			assert false;
			return false;
		}

		if (surroundingScConjunction == null) {
			// has not yet been added to a SetConstraintConjunction, omit the remaining checks
			return true;
		}

		if (surroundingScConjunction.mSurroundingCCSetConstraints == null) {
			// has not yet been added to a SetConstraintConjunction, omit the remaining checks
			return true;
		}

		final CongruenceClosure<ELEM> surrCc = surroundingScConjunction.getCongruenceClosure();

		if (surrCc == null) {
			// has not yet been added to a SetConstraintConjunction with a Cc, omit the remaining checks
			return true;
		}

		if (surrCc.mLiteralSetConstraints == null) {
			return true;
		}


		/*
		 * all elements that his constraint talks about must be known to the surrounding CongruenceClosure instance.
		 */
		if (!mLiterals.stream().allMatch(surrCc::hasElement)) {
			assert false;
			return false;
		}

		// all elements of mNonLiterals must be representatives
		if (mNonLiterals.stream().anyMatch(nl -> !surrCc.isRepresentative(nl))) {
			assert false;
			return false;
		}

		// all expandable elements of mNonLiterals must have been expanded
		for (final ELEM nl : mNonLiterals) {
			final Set<SetConstraint<ELEM>> contCons = surrCc.getContainsConstraintForElement(nl);
			if (contCons != null && SetConstraintConjunction.hasOnlyLiterals(contCons)) {
				assert false;
				return false;
			}
		}

		return true;
	}

//	public void updateOnChangedRepresentatives(final CongruenceClosure<ELEM> congruenceClosure) {
//		{
//			final Set<ELEM> newLiterals = new HashSet<>();
//			for (final ELEM lit : mLiterals) {
//				newLiterals.add(congruenceClosure.getRepresentativeElement(lit));
//			}
//			mLiterals.clear();
//			mLiterals.addAll(newLiterals);
//		}
//		{
//			final Set<ELEM> newNonLiterals = new HashSet<>();
//			for (final ELEM lit : mNonLiterals) {
//				newNonLiterals.add(congruenceClosure.getRepresentativeElement(lit));
//			}
//			mNonLiterals.clear();
//			mNonLiterals.addAll(newNonLiterals);
//		}
//	}

	@Deprecated
	public static <ELEM extends ICongruenceClosureElement<ELEM>> boolean
			isTautological(final ELEM constrainedElement, final SetConstraint<ELEM> sc) {
		assert sc != null;
		return sc.isSingleton() && sc.getSingletonValue().equals(constrainedElement);
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> SetConstraint<ELEM> getInconsistentSetConstraint() {
		return new SetConstraint<>(true);
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> SetConstraint<ELEM>
			updateOnChangedRepresentative(final SetConstraint<ELEM> sc, final CongruenceClosure<ELEM> newCc) {
		// literals never go from non-representative to representative..
		final Set<ELEM> newLiterals = new HashSet<>(sc.getLiterals());
		final Set<ELEM> newNonLiterals = new HashSet<>();
		boolean madeChanges = false;
		for (final ELEM e : sc.mNonLiterals) {
			final ELEM newRep = newCc.getRepresentativeElement(e);
			madeChanges |= e != newRep;
			if (newRep.isLiteral()) {
				newLiterals.add(newRep);
			} else {
				newNonLiterals.add(newRep);
			}
		}
		if (!madeChanges) {
			return sc;
		}
		return buildSetConstraint(newLiterals, newNonLiterals);
	}

	public Set<ELEM> getNonLiterals() {
		return Collections.unmodifiableSet(mNonLiterals);
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> SetConstraint<ELEM>
			expandNonLiteral(final SetConstraint<ELEM> oldSc, final ELEM e, final Set<ELEM> expansion) {
		assert oldSc.getNonLiterals().contains(e);
		final Set<ELEM> newLiterals = new HashSet<>(oldSc.getLiterals());
		final Set<ELEM> newNonLiterals = new HashSet<>(oldSc.getNonLiterals());
		newLiterals.addAll(expansion);
		newNonLiterals.remove(e);
		return buildSetConstraint(newLiterals, newNonLiterals);
	}
}

class SingletonSetConstraint<ELEM extends ICongruenceClosureElement<ELEM>>
 	extends SetConstraint<ELEM> {

//	public SingletonSetConstraint(final SetConstraintConjunction<ELEM> surroundingSetConstraints,
//			final SingletonSetConstraint<ELEM> sc) {
//		super(surroundingSetConstraints, sc);
//	}

	public SingletonSetConstraint(//final SetConstraintConjunction<ELEM> surroundingSetConstraints,
			final ELEM singletonElement) {
		super(//surroundingSetConstraints,
				singletonElement.isLiteral()
					? new HashSet<>(Collections.singleton(singletonElement)) : Collections.emptySet(),
				singletonElement.isLiteral()
					? Collections.emptySet() : new HashSet<>(Collections.singleton(singletonElement))
						);
	}
}