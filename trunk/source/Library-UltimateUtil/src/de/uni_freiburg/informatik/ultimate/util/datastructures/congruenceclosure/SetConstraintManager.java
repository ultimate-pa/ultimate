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
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CcManager.CcBmNames;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

public class SetConstraintManager<ELEM extends ICongruenceClosureElement<ELEM>> {

	private final NestedMap2<Set<ELEM>, Set<ELEM>, SetConstraint<ELEM>> mLiteralsToNonLiteralsToSetConstraint;
	private final SetConstraint<ELEM> mInconsistentSetConstraint;
//	private final SetConstraintComparator<ELEM> mSetConstraintComparator;
	private final IPartialComparator<SetConstraint<ELEM>> mSetConstraintComparator;
	private final CcManager<ELEM> mCcManager;

	public SetConstraintManager(final CcManager<ELEM> ccMan) {
		mLiteralsToNonLiteralsToSetConstraint = new NestedMap2<>();
		mInconsistentSetConstraint = new SetConstraint<>(true);
		mSetConstraintComparator = CcSettings.USE_CACHE_FOR_SETCONSTRAINTS ?
				new CachingSetConstraintComparator<>(this) :
				new SetConstraintComparator<>(this);
		mCcManager = ccMan;
	}

	public SetConstraint<ELEM> buildSetConstraint(
			final Set<ELEM> literals,
			final Set<ELEM> nonLiterals) {
		assert literals.stream().allMatch(ELEM::isLiteral);
		assert !nonLiterals.stream().anyMatch(ELEM::isLiteral);

		if (literals.isEmpty() && nonLiterals.isEmpty()) {
			return getInconsistentSetConstraint();
		}

		SetConstraint<ELEM> result = mLiteralsToNonLiteralsToSetConstraint.get(literals, nonLiterals);
		if (result == null) {
			result = new SetConstraint<>(new HashSet<>(literals), new HashSet<>(nonLiterals));
			mLiteralsToNonLiteralsToSetConstraint.put(literals, nonLiterals, result);
		}
		return result;
	}

	private SetConstraint<ELEM> getInconsistentSetConstraint() {
		return mInconsistentSetConstraint;
	}

	public SetConstraint<ELEM> buildSetConstraint(
			final Collection<ELEM> unsortedElements) {
		final Set<ELEM> literals = new HashSet<>();
		final Set<ELEM> nonLiterals = new HashSet<>();
		for (final ELEM el : unsortedElements) {
			if (el.isLiteral()) {
				literals.add(el);
			} else {
				nonLiterals.add(el);
			}
		}
		return buildSetConstraint(
				literals, nonLiterals);
//				unsortedElements.stream().filter(ELEM::isLiteral).collect(Collectors.toSet()),
//				unsortedElements.stream().filter(e -> !e.isLiteral()).collect(Collectors.toSet()));
	}


	//	public void updateOnChangedRepresentative(final ELEM elem1OldRep, final ELEM elem2OldRep, final ELEM newRep) {
	public  SetConstraint<ELEM>
				updateOnChangedRepresentative(final SetConstraint<ELEM> oldSetConstraint,
			final ELEM elem1OldRep, final ELEM elem2OldRep, final ELEM newRep) {

		final Set<ELEM> oldElements = oldSetConstraint.getElementSet();
		if (!oldElements.contains(elem1OldRep) && !oldElements.contains(elem2OldRep)) {
			return oldSetConstraint;
		}

		final Set<ELEM> newLiterals = new HashSet<>(oldSetConstraint.getLiterals());
		final Set<ELEM> newNonLiterals = new HashSet<>(oldSetConstraint.getNonLiterals());

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

	public  SetConstraint<ELEM>
	 		updateOnChangedRepresentative(final SetConstraint<ELEM> oldSetConstraint, final ELEM oldRep, final ELEM newRep) {

		final Set<ELEM> oldElements = oldSetConstraint.getElementSet();
		if (!oldElements.contains(oldRep)) {
			return oldSetConstraint;
		}

		final Set<ELEM> newLiterals = new HashSet<>(oldSetConstraint.getLiterals());
		final Set<ELEM> newNonLiterals = new HashSet<>(oldSetConstraint.getNonLiterals());

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

	public SetConstraint<ELEM> updateOnChangedRepresentative(final SetConstraint<ELEM> sc,
			final CongruenceClosure<ELEM> newCc) {
		// literals never go from non-representative to representative..
		final Set<ELEM> newLiterals = new HashSet<>(sc.getLiterals());
		final Set<ELEM> newNonLiterals = new HashSet<>();
		boolean madeChanges = false;
		for (final ELEM e : sc.getNonLiterals()) {
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

	public  SetConstraint<ELEM>
			filterWithDisequality(final SetConstraint<ELEM> constraint, final ELEM elem) {
//		assert mSurroundingScConjunction.getCongruenceClosure().isRepresentative(elem);
//		mLiterals.remove(elem);
//		mNonLiterals.remove(elem);

		if (!constraint.getLiterals().contains(elem) && !constraint.getNonLiterals().contains(elem)) {
			return constraint;
		}

		final Set<ELEM> newLiterals = new HashSet<>(constraint.getLiterals());
		final Set<ELEM> newNonLiterals = new HashSet<>(constraint.getNonLiterals());
		newLiterals.remove(elem);
		newNonLiterals.remove(elem);
		return buildSetConstraint(newLiterals, newNonLiterals);
	}


	public  SetConstraint<ELEM>
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


	/**
	 * Apply propagation rule
	 *  e in L /\ e != l --> e in L\{l}
	 *
	 * Work inplace except if constraint becomes inconsistent or a singleton
	 */
	public  SetConstraint<ELEM>
			filterWithDisequalities(final SetConstraint<ELEM> oldConstraint, final ELEM constrainedElement,
					final CongruenceClosure<ELEM> congruenceClosure) {

		boolean madeChanges = false;

		final Set<ELEM> newLiterals = new HashSet<>(oldConstraint.getLiterals());
		{

			for (final ELEM lit : oldConstraint.getLiterals()) {
				/*
				 * rule: e in L /\ e != l --> e in L\{l}
				 */
				if (congruenceClosure.getEqualityStatus(constrainedElement, lit) == EqualityStatus.NOT_EQUAL) {
					madeChanges |= newLiterals.remove(lit);
				}
			}
		}
		final Set<ELEM> newNonLiterals = new HashSet<>(oldConstraint.getNonLiterals());
		{

			for (final ELEM lit : oldConstraint.getNonLiterals()) {
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

		return buildSetConstraint(newLiterals, newNonLiterals);
	}


	public  boolean isStrongerThan(
			final SetConstraint<ELEM> lhsConjunct, final SetConstraint<ELEM> rhsConjunct) {
		if (!rhsConjunct.getLiterals().containsAll(lhsConjunct.getLiterals())) {
			return false;
		}
		if (!rhsConjunct.getNonLiterals().containsAll(lhsConjunct.getNonLiterals())) {
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
	public  SetConstraint<ELEM> meet(
			final CCLiteralSetConstraints<ELEM> surroundingSetConstraints,
			final Collection<SetConstraint<ELEM>> scs) {
		if (scs.isEmpty()) {
			// empty meet --> "Top" constraint --> represented by "null"
			return null;
		}

		final Iterator<SetConstraint<ELEM>> scIt = scs.iterator();

		final SetConstraint<ELEM> firstSc = scIt.next();

		Set<ELEM> literals = new HashSet<>(firstSc.getLiterals());
		final Set<ELEM> nonLiterals = new HashSet<>(firstSc.getNonLiterals());

		while (scIt.hasNext()) {
			final SetConstraint<ELEM> current = scIt.next();

			// TODO: is this a good implementation of intersection??
			final Set<ELEM> newLiterals = new HashSet<>();
			for (final ELEM l : literals) {
				if (current.getLiterals().contains(l)) {
					newLiterals.add(l);
				}
			}
			literals = newLiterals;


			nonLiterals.addAll(current.getNonLiterals());
		}

//		final SetConstraintConjunction<ELEM> surroundingSetCc = firstSc.mSurroundingScConjunction;
//		final CCLiteralSetConstraints<ELEM> surroundingSetCc =
//				firstSc.mSurroundingScConjunction.mSurroundingCCSetConstraints;
		return buildSetConstraint(//surroundingSetConstraints,
				literals, nonLiterals);
	}



	public  SetConstraint<ELEM> join(
			final SetConstraint<ELEM> sc1, final SetConstraint<ELEM> sc2) {
		return buildSetConstraint(
				DataStructureUtils.union(sc1.getLiterals(), sc2.getLiterals()),
				DataStructureUtils.union(sc1.getNonLiterals(), sc2.getNonLiterals()));
	}

	public SetConstraint<ELEM>
		expandNonLiteral(final SetConstraint<ELEM> oldSc, final ELEM e, final Set<ELEM> expansion) {
		assert oldSc.getNonLiterals().contains(e);
		final Set<ELEM> newLiterals = new HashSet<>(oldSc.getLiterals());
		final Set<ELEM> newNonLiterals = new HashSet<>(oldSc.getNonLiterals());
		newLiterals.addAll(expansion);
		newNonLiterals.remove(e);
		return buildSetConstraint(newLiterals, newNonLiterals);
	}


	//////////////////////////////////////////////

	public  Set<SetConstraint<ELEM>> updateOnChangedRepresentative(
			final Set<SetConstraint<ELEM>> setConstraints, final ELEM oldRep,
			final ELEM newRep) {
		final Set<SetConstraint<ELEM>> result = new HashSet<>();
		for (final SetConstraint<ELEM> setConstraint : setConstraints) {
			result.add(updateOnChangedRepresentative(setConstraint, oldRep, newRep));
		}
		return result;
	}

	public  Set<SetConstraint<ELEM>> updateOnChangedRepresentative(
			final Set<SetConstraint<ELEM>> setConstraints, final ELEM elem1OldRep, final ELEM elem2OldRep,
			final ELEM newRep) {
		final Set<SetConstraint<ELEM>> result = new HashSet<>();
		boolean madeChanges = false;
		for (final SetConstraint<ELEM> setConstraint : setConstraints) {
			final SetConstraint<ELEM> updated =
					updateOnChangedRepresentative(setConstraint, elem1OldRep, elem2OldRep, newRep);
			madeChanges |= updated != setConstraint;
			result.add(updated);
		}
		if (!madeChanges) {
			return setConstraints;
		}
		return result;
	}

	public  Set<SetConstraint<ELEM>> transformElements(
			final Set<SetConstraint<ELEM>> setConstraints, final Function<ELEM, ELEM> elemTransformer) {
		final Set<SetConstraint<ELEM>> result = new HashSet<>();
		for (final SetConstraint<ELEM> setConstraint : setConstraints) {
			result.add(transformElements(setConstraint, elemTransformer));
		}
		return result;
	}

	/**
	 *
	 * @param surroundingConstraint
	 * @param rep1
	 * @param rep2
	 * @param constraintConjunction1
	 * @param constraintConjunction2
	 * @return
	 */
	public  Set<SetConstraint<ELEM>> meet(
			final CCLiteralSetConstraints<ELEM> surroundingConstraint,
			final Set<SetConstraint<ELEM>> constraintConjunction1,
			final Set<SetConstraint<ELEM>> constraintConjunction2) {
		if (isTautological(constraintConjunction1)) {
			return constraintConjunction2;
		}
		if (isTautological(constraintConjunction2)) {
			return constraintConjunction1;
		}
		if (isInconsistent(constraintConjunction1)) {
			return getInconsistentSetConstraintConjunction();
		}
		if (isInconsistent(constraintConjunction2)) {
			return getInconsistentSetConstraintConjunction();
		}

		final Collection<SetConstraint<ELEM>> newSetConstraints = DataStructureUtils.union(constraintConjunction1,
				constraintConjunction2);

		return surroundingConstraint.getCongruenceClosure().getManager()
				.normalizeSetConstraintConjunction(surroundingConstraint, newSetConstraints);
	}

	/**
	 * Check if the two constraints would contradict "if they were about the same
	 * element". (Used in getEqualityStatus..)
	 *
	 * assumes (like all methods of this kind) that the SetConstraints are aligned in terms of representatives
	 *
	 * @param litConstraint1
	 * @param litConstraint2
	 * @return
	 */
	public boolean meetIsInconsistent(
			final CCLiteralSetConstraints<ELEM> surroundingConstraint,
			final Set<SetConstraint<ELEM>> litConstraint1,
			final Set<SetConstraint<ELEM>> litConstraint2) {

		mCcManager.bmStart(CcBmNames.MEET_IS_INCONSISTENT);


		SetConstraint<ELEM> lits1 = null;
		for (final SetConstraint<ELEM> sc : litConstraint1) {
			if (sc.hasOnlyLiterals()) {
				lits1 = sc;
				break;
			}
		}
		if (lits1 == null) {
			mCcManager.bmEnd(CcBmNames.MEET_IS_INCONSISTENT);
			return false;
		}
		SetConstraint<ELEM> lits2 = null;
		for (final SetConstraint<ELEM> sc : litConstraint2) {
			if (sc.hasOnlyLiterals()) {
				lits2 = sc;
				break;
			}
		}
		if (lits2 == null) {
			mCcManager.bmEnd(CcBmNames.MEET_IS_INCONSISTENT);
			return false;
		}

//		final SetConstraint<ELEM> lits1;
//		{
//			final Stream<SetConstraint<ELEM>> onlyLits1 = litConstraint1.stream().filter(sc -> sc.hasOnlyLiterals());
//			assert onlyLits1.collect(Collectors.toList()).size() <= 1 : "not normalized correctly";
//			try {
//				lits1 = onlyLits1.findAny().get();
//			} catch (final NoSuchElementException ex) {
//				mCcManager.bmEnd(CcBmNames.MEET_IS_INCONSISTENT);
//				return false;
//			}
//		}
//		final SetConstraint<ELEM> lits2;
//		{
//			final Stream<SetConstraint<ELEM>> onlyLits2 = litConstraint1.stream().filter(sc -> sc.hasOnlyLiterals());
//			assert onlyLits2.collect(Collectors.toList()).size() <= 1 : "not normalized correctly";
//			try {
//				lits2 = onlyLits2.findAny().get();
//			} catch (final NoSuchElementException ex) {
//				mCcManager.bmEnd(CcBmNames.MEET_IS_INCONSISTENT);
//				return false;
//			}
//		}
//		final boolean result = DataStructureUtils.intersection(lits1.getLiterals(), lits2.getLiterals()).isEmpty();
		final boolean result = !DataStructureUtils.haveNonEmptyIntersection(lits1.getLiterals(), lits2.getLiterals());

//		final Collection<SetConstraint<ELEM>> meet = meet(surroundingConstraint, litConstraint1,
//				litConstraint2);
//		final boolean result = isInconsistent(meet);
		mCcManager.bmEnd(CcBmNames.MEET_IS_INCONSISTENT);
		return result;
	}

	/**
	 * Can deal with "null" arguments (which represent the "Top" value).
	 *
	 * Basic law for this:
	 *  |= A /\ B --> C /\ D
	 *    iff
	 *   |= A /\ B --> C
	 *     and
	 *   |= A /\ B --> D
	 *
	 * That means we can build the meet of the input SetCcs in any detail we want, involving the usual power set
	 * construction, and perhaps filtering, or we can assume this has been done (should be the case, at the moment,
	 * as the Set<SetConstraint<ELEM>> come from SetConstraintConjunction<ELEM>, which have that property).
	 * Then we check one by one for inclusion of the set constraints.
	 *
	 * @param constraintConjunction1
	 * @param constraintConjunction2
	 * @return
	 */
	public  boolean isStrongerThan(
			final Set<SetConstraint<ELEM>> constraintConjunction1,
			final Set<SetConstraint<ELEM>> constraintConjunction2) {
		if (isTautological(constraintConjunction1)) {
			// cc2 = Top
			return true;
		}
		if (isTautological(constraintConjunction2)) {
			// cc1 = Top, cc2 != Top
			return false;
		}
		if (isInconsistent(constraintConjunction1)) {
			// cc1 = Bot
			return true;
		}
		if (isInconsistent(constraintConjunction2)) {
			// cc2 = Bot, cc1 != Bot
			return false;
		}

		for (final SetConstraint<ELEM> rhsConjunct : constraintConjunction2) {

			boolean disjunctionHolds = false;
			for (final SetConstraint<ELEM> lhsConjunct : constraintConjunction1) {
				if (!isStrongerThan(lhsConjunct, rhsConjunct)) {
					disjunctionHolds = true;
					break;
				}
			}

			if (disjunctionHolds) {
				continue;
			} else {
				return false;
			}
		}

		return true;
	}

	public  Set<SetConstraint<ELEM>> getInconsistentSetConstraintConjunction() {
		return Collections.singleton(SetConstraint.getInconsistentSetConstraint());
	}

	public  Set<SetConstraint<ELEM>> getTautologicalSetConstraintConjunction() {
		return Collections.emptySet();
	}

	public  Set<SetConstraint<ELEM>> join(
			final CCLiteralSetConstraints<ELEM> surroundingSetConstraints,
			final Set<SetConstraint<ELEM>> constraintConjunction1,
			final Set<SetConstraint<ELEM>> constraintConjunction2) {
		if (isTautological(constraintConjunction1)) {
			return getTautologicalSetConstraintConjunction();
		}
		if (isTautological(constraintConjunction2)) {
			return getTautologicalSetConstraintConjunction();
		}
		if (isInconsistent(constraintConjunction1)) {
			return constraintConjunction2;
		}
		if (isInconsistent(constraintConjunction2)) {
			return constraintConjunction1;
		}
		final Set<SetConstraint<ELEM>> newSetConstraints = new HashSet<>();

		for (final SetConstraint<ELEM> sc1 : constraintConjunction1) {
			for (final SetConstraint<ELEM> sc2 : constraintConjunction2) {
				newSetConstraints.add(join(sc1, sc2));
			}
		}

		return newSetConstraints;
	}

	/**
	 * assumes that representatives are resolved..
	 *
	 * @param constraints
	 * @return
	 */
	public static <ELEM extends ICongruenceClosureElement<ELEM>> boolean isTautological(
			final Set<SetConstraint<ELEM>> constraints) {
		if (constraints == null) {
			return true;
		}
		if (constraints.isEmpty()) {
			return true;
		}
		return false;
	}

	public boolean isInconsistent(final Collection<SetConstraint<ELEM>> constraints) {
		if (constraints == null) {
			return false;
		}
		for (final SetConstraint<ELEM> sc : constraints) {
			if (sc.isInconsistent()) {
				return true;
			}
		}
		return false;
//		return constraints.stream().anyMatch(sc -> sc.isInconsistent());
	}

	public  Set<ELEM> getSingletonValues(final Set<SetConstraint<ELEM>> constraints) {
		final Set<ELEM> result = new HashSet<>();
		for (final SetConstraint<ELEM> sc : constraints) {
			if (sc.isSingleton()) {
				result.add(sc.getSingletonValue());
			}
		}
		return result;
//		return constraints.stream().filter(sc -> sc.isSingleton())
//				.map(sc -> sc.getSingletonValue())
//				.collect(Collectors.toSet());
	}

	public  Set<SetConstraint<ELEM>> filterWithDisequalities(
			final CongruenceClosure<ELEM> congruenceClosure, final ELEM constrainedElement,
			final Set<SetConstraint<ELEM>> constraints) {
		final Set<SetConstraint<ELEM>> result = new HashSet<>();
		boolean madeChanges = false;
		for (final SetConstraint<ELEM> setConstraint : constraints) {
			final SetConstraint<ELEM> filtered = filterWithDisequalities(setConstraint,
					constrainedElement, congruenceClosure);
			madeChanges |= filtered != setConstraint;
			result.add(filtered);
		}
		if (!madeChanges) {
			return constraints;
		}
		return result;
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> boolean isTautological(
			final SetConstraintConjunction<ELEM> newConstraint) {
		if (newConstraint == null) {
			return true;
		}
		if (newConstraint.isTautological()) {
			return true;
		}
		return false;
	}

	public  Set<SetConstraint<ELEM>>
			filterWithDisequality(final Set<SetConstraint<ELEM>> setConstraints, final ELEM elem) {
		final Set<SetConstraint<ELEM>> result = new HashSet<>();
		boolean madeChanges = false;
		for (final SetConstraint<ELEM> sc : setConstraints) {
			final SetConstraint<ELEM> filtered = filterWithDisequality(sc, elem);
			madeChanges |= filtered != sc;
			result.add(filtered);
		}
		if (!madeChanges) {
			return setConstraints;
		}
		return result;
	}

	public Set<SetConstraint<ELEM>> updateOnChangedRepresentative(final Set<SetConstraint<ELEM>> oldConstraint,
					final CongruenceClosure<ELEM> newCc) {
		if (oldConstraint == null) {
			return null;
		}

		final Set<SetConstraint<ELEM>> result = new HashSet<>();
		boolean madeChanges = false;
		for (final SetConstraint<ELEM> sc : oldConstraint) {
			final SetConstraint<ELEM> updRep = updateOnChangedRepresentative(sc, newCc);
			madeChanges |= updRep != sc;
			result.add(updRep);
		}

		if (!madeChanges) {
			// TODO extra wrapping is not nice
			return oldConstraint;
		}
		return result;
	}

	public IPartialComparator<SetConstraint<ELEM>> getSetConstraintComparator() {
		return mSetConstraintComparator;
	}

//	public boolean hasOnlyLiterals(final Set<SetConstraint<ELEM>> litConstraint2) {
//		if (litConstraint2 == null || litConstraint2.isEmpty()) {
//			return false;
//		}
//		return litConstraint2.stream().allMatch(sc -> sc.hasOnlyLiterals());
//	}


	/**
	 * Detect if a conjunction of SetConstraints constraints to be only in a set of literals.
	 * If that is the case return that set, otherwise return null.
	 *
	 * @param scs
	 * @return
	 */
	public Set<ELEM> getLiteralSet(final Set<SetConstraint<ELEM>> scs) {
		assert scs.stream().filter(SetConstraint::hasOnlyLiterals).collect(Collectors.toList()).size() <= 1 :
			"not normalized?";
		for (final SetConstraint<ELEM> sc : scs) {
			if (sc.hasOnlyLiterals()) {
				return sc.getLiterals();
			}
		}
		return null;
	}

	/**
	 * Use this when we first bring together an element and the conjunction of SetConstraints that it is supposed to be
	 * contained in.
	 * The combination is tautological if the element is contained in all SetConstraints (or if the set is empty)
	 *
	 * @param elem
	 * @param constraint
	 * @return
	 */
	public static <ELEM extends ICongruenceClosureElement<ELEM>> boolean isTautologicalWrtElement(
			final ELEM elem, final Set<SetConstraint<ELEM>> constraint) {
		if (isTautological(constraint)) {
			// constraint is tautological by itself (i.e. null or an empty conjunction)
			return true;
		}
		for (final SetConstraint<ELEM> sc : constraint) {
			if (!sc.containsElement(elem)) {
				// sc only has element other than elem --> it is not tautological to state "elem in sc"
				return false;
			}
		}
		return true;
	}

}
