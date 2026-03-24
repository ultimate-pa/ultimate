/*
 * Copyright (C) 2009-2026 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Polynomial;

class AddTermITEAxiom implements Operation {

	/**
	 * The clausifier.
	 */
	private final Clausifier mClausifier;
	private final SourceAnnotation mSource;

	/**
	 * The ite term for which we add the axioms.
	 */
	private final Term mTermITE;

	/**
	 * Checks if all branches only differ by a constant value. In this case we
	 * create bound constraints of the form (<= minValue ite) and (<= ite maxValue).
	 */
	boolean mIsNotConstant = false;
	/**
	 * The minimum value of all branches visited so far. This is initially set to
	 * null. Set to null if mIsNotConstant is true.
	 */
	private Term mMinValue = null;
	/**
	 * The difference between minimum and maximum value visited so far. Set to null
	 * if mIsNotConstant is true.
	 */
	private Rational mMaxSubMin = null;
	/**
	 * The already visited sub terms. Used for bound checking, to avoid exponential
	 * blow-up.
	 */
	private final Set<Term> mVisited = new HashSet<>();

	public AddTermITEAxiom(Clausifier clausifier, final Term termITE, final SourceAnnotation source) {
		mClausifier = clausifier;
		mTermITE = termITE;
		mSource = source;
	}

	@Override
	public void perform() {
		mClausifier.pushOperation(new CollectConditions(new LinkedHashSet<Term>(), mTermITE));
		mClausifier.pushOperation(new AddBoundAxioms());
		mClausifier.pushOperation(new CheckBounds(mTermITE));
	}

	private class CollectConditions implements Operation {
		private final LinkedHashSet<Term> mConds;
		private final Term mTerm;

		public CollectConditions(final LinkedHashSet<Term> conds, final Term term) {
			mConds = conds;
			mTerm = term;
		}

		@Override
		public void perform() {
			if (mTerm instanceof ApplicationTerm) {
				final ApplicationTerm at = (ApplicationTerm) mTerm;
				if (at.getFunction().getName().equals("ite")
						&& (at.mTmpCtr <= Config.OCC_INLINE_TERMITE_THRESHOLD || mConds.size() == 0)) {
					final Term t = at.getParameters()[1];
					final Term e = at.getParameters()[2];
					Term c = at.getParameters()[0];
					boolean isNegated = false;
					while (Clausifier.isNotTerm(c)) {
						c = ((ApplicationTerm) c).getParameters()[0];
						isNegated = !isNegated;
					}
					final Term notC = c.getTheory().term(SMTLIBConstants.NOT, c);
					if (mConds.contains(c)) {
						mClausifier.pushOperation(new CollectConditions(mConds, isNegated ? t : e));
					} else if (mConds.contains(notC)) {
						mClausifier.pushOperation(new CollectConditions(mConds, isNegated ? e : t));
					} else {
						final LinkedHashSet<Term> other = new LinkedHashSet<>(mConds);
						mConds.add(isNegated ? c : notC);
						other.add(isNegated ? notC : c);
						mClausifier.pushOperation(new CollectConditions(mConds, t));
						mClausifier.pushOperation(new CollectConditions(other, e));
					}
					return;
				}
			}
			// Not a nested ite term or a nested shared ite term
			final Theory theory = mTerm.getTheory();
			final Term[] literals = new Term[mConds.size() + 1];
			int offset = mConds.size();
			for (final Term cond : mConds) {
				literals[--offset] = cond;
			}
			literals[mConds.size()] = theory.term("=", mTermITE, mTerm);
			mClausifier.buildTautology(theory, literals, ProofConstants.TAUT_TERM_ITE, mSource);
		}
	}

	private class CheckBounds implements Operation {
		private final Term mTerm;

		public CheckBounds(final Term term) {
			mTerm = term;
		}

		@Override
		public void perform() {
			if (mIsNotConstant || !mVisited.add(mTerm)) {
				// already seen
				return;
			}
			if (mTerm instanceof ApplicationTerm) {
				final ApplicationTerm at = (ApplicationTerm) mTerm;
				if (at.getFunction().getName().equals("ite")) {
					final Term t = at.getParameters()[1];
					final Term e = at.getParameters()[2];
					mClausifier.pushOperation(new CheckBounds(t));
					mClausifier.pushOperation(new CheckBounds(e));
					return;
				}
			}
			// Not a nested ite term or a nested shared ite term
			// if this is the first term, just store it.
			if (mMinValue == null) {
				mMinValue = mTerm;
				mMaxSubMin = Rational.ZERO;
				return;
			}
			final Polynomial diff = new Polynomial(mTerm);
			diff.add(Rational.MONE, mMinValue);
			if (!diff.isConstant()) {
				mIsNotConstant = true;
				return;
			}
			if (diff.getConstant().signum() < 0) {
				mMinValue = mTerm;
				mMaxSubMin = mMaxSubMin.sub(diff.getConstant());
			} else if (diff.getConstant().compareTo(mMaxSubMin) > 0) {
				mMaxSubMin = diff.getConstant();
			}
		}
	}

	private class AddBoundAxioms implements Operation {

		public AddBoundAxioms() {
		}

		@Override
		public void perform() {
			if (!mIsNotConstant && mMinValue != null) {
				// ite term is bounded by mMinValue and mMinValue + mMaxSubMin
				final Sort sort = mTermITE.getSort();
				final Theory theory = sort.getTheory();
				final Term zero = Rational.ZERO.toTerm(sort);
				final Polynomial diff = new Polynomial(mMinValue);
				diff.add(Rational.MONE, mTermITE);
				final Term lboundAx = theory.term("<=", mClausifier.mCompiler.unifyPolynomial(diff, sort), zero);
				mClausifier.buildClause(mClausifier.mTracker.tautology(lboundAx, ProofConstants.TAUT_TERM_ITE_BOUND),
						mSource);
				diff.add(mMaxSubMin);
				diff.mul(Rational.MONE);
				final Term uboundAx = theory.term("<=", mClausifier.mCompiler.unifyPolynomial(diff, sort), zero);
				mClausifier.buildClause(mClausifier.mTracker.tautology(uboundAx, ProofConstants.TAUT_TERM_ITE_BOUND),
						mSource);
			}
		}
	}
}