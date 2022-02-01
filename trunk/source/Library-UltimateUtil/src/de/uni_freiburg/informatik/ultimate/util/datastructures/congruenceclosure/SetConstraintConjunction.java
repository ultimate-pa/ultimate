package de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

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

//		final List<SetConstraint<ELEM>> onlyLits =
//				setConstraintsRaw.stream().filter(SetConstraint::hasOnlyLiterals).collect(Collectors.toList());
		final List<SetConstraint<ELEM>> onlyLits = new ArrayList<>();
		for (final SetConstraint<ELEM> sc : setConstraintsRaw) {
			if (sc.hasOnlyLiterals()) {
				onlyLits.add(sc);
			}
		}

		assert onlyLits.size() < 2;
		if (onlyLits.size() == 1) {
			mScWithOnlyLiterals = onlyLits.iterator().next();
		} else {
			mScWithOnlyLiterals = null;
		}

		mSetConstraints = Collections.unmodifiableSet(new HashSet<>(setConstraintsRaw));
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
//		return mIsInconsistent || mSetConstraints.stream().anyMatch(sc -> sc.isInconsistent());
		if (mIsInconsistent) {
			return true;
		}
		for (final SetConstraint<ELEM> sc : mSetConstraints) {
			if (sc.isInconsistent()) {
				return true;
			}
		}
		return false;
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
//		return setConstraints.stream().anyMatch(sc -> sc.hasOnlyLiterals());
		for (final SetConstraint<ELEM> sc : setConstraints) {
			if (sc.hasOnlyLiterals()) {
				return true;
			}
		}
		return false;
	}

	public Set<ELEM> getLiterals() {
		assert mScWithOnlyLiterals.getNonLiterals().isEmpty();
		return mScWithOnlyLiterals.getLiterals();
	}

//	public static <ELEM extends ICongruenceClosureElement<ELEM>> Set<ELEM> getLiterals(
//			final Collection<SetConstraint<ELEM>> setConstraints) {
//		assert setConstraints.stream().filter(sc -> sc.hasOnlyLiterals()).collect(Collectors.toSet()).size() == 1;
//		for (final SetConstraint<ELEM> sc : setConstraints) {
//			if (sc.hasOnlyLiterals()) {
//				return sc.getLiterals();
//			}
//		}
//		throw new IllegalStateException("check for hasOnlyLiterals before calling this");
//	}

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
}
