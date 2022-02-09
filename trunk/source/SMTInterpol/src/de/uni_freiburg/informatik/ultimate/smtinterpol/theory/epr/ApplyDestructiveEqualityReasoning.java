package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom.TrueAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.NamedAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;

/**
 * Apply destructive equality reasoning to the clause consisting of the
 * given literals. Procedure: - build one big substitution which has one
 * entry for each equality - apply the subtitution to each (quantified)
 * literal in the clause (it may be a bit suprising that this works, but I
 * think it does, example: {x != c, x != d, P(x)} will yield the
 * substitution [x <- c, x <- d], which will yield the clause {c != c, c !=
 * d, P(c)} which seems right.) //TODO: make sure..
 *
 * TODO: some of the transformations made here might be undone by "constructive
 * equality reasoning" afterwards, namely those that introduce repeating variables
 * into one literal. -- avoid those transformations up front, perhaps..
 */
class ApplyDestructiveEqualityReasoning {

	HashSet<Literal> mResult;
	boolean mIsResultGround = true;
	final private EprTheory mEprTheory;

	public ApplyDestructiveEqualityReasoning(final EprTheory eprTheory, final Literal[] literals) {
		assert eprTheory != null;
		mEprTheory = eprTheory;
		applyDER(new HashSet<>(Arrays.asList(literals)));
	}

	private void applyDER(final HashSet<Literal> literals) {
		HashSet<Literal> currentClause = new HashSet<>(literals);
		Literal disEquality = findDisequality(currentClause);
		mResult = currentClause;
		mIsResultGround = false;
		while (disEquality != null) {
			currentClause.remove(disEquality);

			final TTSubstitution sub = extractSubstitutionFromEquality((EprQuantifiedEqualityAtom) disEquality.getAtom());

			mResult = new HashSet<>();
			mIsResultGround = true;
			for (final Literal l : currentClause) {
				final Literal sl = EprHelpers.applySubstitution(sub, l, mEprTheory, true);
				if (sl.getAtom() instanceof TrueAtom) {
					if (sl.getSign() == 1) {
						// do nothing/just add it to the result (tautology
						// will be detected later)
					} else {
						continue; // omit "false"
					}
				} else if (sl.getAtom() instanceof EprQuantifiedEqualityAtom
						|| sl.getAtom() instanceof EprQuantifiedPredicateAtom) {
					mIsResultGround = false;
				} else if (sl.getAtom() instanceof EprGroundPredicateAtom || sl.getAtom() instanceof CCEquality) {
					mEprTheory.addAtomToDPLLEngine(sl.getAtom());
				} else if (sl.getAtom() instanceof NamedAtom) {
					// do nothing/just add it to the result
				} else {
					assert false : "case not forseen..";
				}
				mResult.add(sl);
			}
			currentClause = mResult;

			disEquality = findDisequality(currentClause);
		}
	}

	public TTSubstitution extractSubstitutionFromEquality(final EprQuantifiedEqualityAtom eea) {
		final TermTuple tt = eea.getArgumentsAsTermTuple();
		TermVariable tv = null;
		Term t = null;
		if (tt.terms[0] instanceof TermVariable) {
			tv = (TermVariable) tt.terms[0];
			t = tt.terms[1];
		} else {
			tv = (TermVariable) tt.terms[1];
			t = tt.terms[0];
		}
		return new TTSubstitution(tv, t);
	}

	private Literal findDisequality(final HashSet<Literal> literals) {
		for (final Literal l : literals) {
			if (l.getSign() != 1 && l.getAtom() instanceof EprQuantifiedEqualityAtom) {
				return l;
			}
		}
		return null;
	}

	/**
	 * Applies sub to li and adds the resulting Literal to newLits. Also
	 * updates mIsResultGround (i.e. when a Literal remains non-ground, it
	 * is set to false)
	 *
	 * @param sub
	 *            substitution to be applied
	 * @param newLits
	 *            set to add to
	 * @param li
	 *            literal whose variables should be substituted
	 */
	public Literal getSubstitutedLiteral(final TTSubstitution sub, final Literal li) {
		if (li.getAtom() instanceof EprQuantifiedPredicateAtom
				|| li.getAtom() instanceof EprQuantifiedEqualityAtom) {
			final boolean liPositive = li.getSign() == 1;
			final TermTuple liTT = ((EprAtom) li.getAtom()).getArgumentsAsTermTuple();
			final SourceAnnotation source = ((EprAtom) li.getAtom()).getSourceAnnotation();

			final TermTuple newTT = sub.apply(liTT);

			if (newTT.equals(liTT)) {
				return li;
			}

			if (li.getAtom() instanceof EprQuantifiedEqualityAtom) {
				if (newTT.isGround()) {
					if (newTT.terms[0] == newTT.terms[1] && liPositive) {
						return new DPLLAtom.TrueAtom();
					} else if (newTT.terms[0] == newTT.terms[1] && !liPositive) {
						return new DPLLAtom.TrueAtom().negate();
					}
					// how to obtain a fresh CCEquality???
					throw new UnsupportedOperationException();
				} else {
					// TODO use good hash
					final EprQuantifiedEqualityAtom eea =
							new EprQuantifiedEqualityAtom(
									(ApplicationTerm) mEprTheory.getTheory().term("=", newTT.terms),
									0,
									li.getAtom().getAssertionStackLevel(),
									mEprTheory.getEqualityEprPredicate(newTT.terms[0].getSort()),
									source);
					return liPositive ? eea : eea.negate();
				}
			} else {
				final EprPredicate liPred = ((EprQuantifiedPredicateAtom) li.getAtom()).getEprPredicate();

				EprAtom ea = null;
				if (newTT.isGround()) {
					ea = liPred.getAtomForTermTuple(newTT, mEprTheory.getTheory(),
							mEprTheory.getClausifier().getStackLevel(), source);
				} else {
					ea = liPred.getAtomForTermTuple(newTT, mEprTheory.getTheory(),
							mEprTheory.getClausifier().getStackLevel(), source);
				}
				return liPositive ? ea : ea.negate();
			}
		} else {
			return li;
		}
	}

	public Set<Literal> getResult() {
		return mResult;
	}

	public boolean isResultGround() {
		return mIsResultGround;
	}
}