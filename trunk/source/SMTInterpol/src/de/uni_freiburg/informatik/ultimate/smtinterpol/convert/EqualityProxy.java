/*
 * Copyright (C) 2012 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Polynomial;

public class EqualityProxy {

	/**
	 * Singleton class to represent an equality that is a tautology.
	 * @author Juergen Christ
	 */
	public static final class TrueEqualityProxy extends EqualityProxy {
		private TrueEqualityProxy() {
			super(null, null, null);
		}
		@Override
		public DPLLAtom getLiteral(final SourceAnnotation source) {
			throw new InternalError("Should never be called");
		}
	}
	/**
	 * Singleton class to represent an equality that is unsatisfiable.
	 * @author Juergen Christ
	 */
	public static final class FalseEqualityProxy extends EqualityProxy {
		private FalseEqualityProxy() {
			super(null, null, null);
		}
		@Override
		public DPLLAtom getLiteral(final SourceAnnotation source) {
			throw new InternalError("Should never be called");
		}
	}

	private static final TrueEqualityProxy TRUE = new TrueEqualityProxy();
	private static final FalseEqualityProxy FALSE = new FalseEqualityProxy();

	public static TrueEqualityProxy getTrueProxy() {
		return TRUE;
	}

	public static FalseEqualityProxy getFalseProxy() {
		return FALSE;
	}

	final Clausifier mClausifier;
	final Term mLhs, mRhs;

	public EqualityProxy(final Clausifier clausifier, final Term lhs, final Term rhs) {
		mClausifier = clausifier;
		mLhs = lhs;
		mRhs = rhs;
	}

	public LAEquality createLAEquality() {
		/* create la part */
		final Polynomial affine = new Polynomial(mLhs);
		affine.add(Rational.MONE, mRhs);
		return mClausifier.getLASolver().createEquality(mClausifier.createMutableAffinTerm(affine, null));
	}

	public Rational computeNormFactor(final Term lhs, final Term rhs) {
		final Polynomial affine = new Polynomial(lhs);
		affine.add(Rational.MONE, rhs);
		return affine.getGcd().inverse();
	}

	/**
	 * Creates a CCEquality for the given lhs and rhs.  The equality must
	 * match this EqualityFormula, i.e.,
	 * <code>lhs-rhs = c*(this.lhs-this.rhs)</code> for some rational c.
	 * This also has as side-effect, that it creates an LAEquality if it
	 * did not exists before.  For this reason it is only allowed to call
	 * it for integer or real terms. It will register LAEquality and CCEquality
	 * with each other.
	 * @param lhs the left hand side.
	 * @param rhs the right hand side.
	 * @return The created (or cached) CCEquality.
	 */
	public CCEquality createCCEquality(final Term lhs, final Term rhs) {
		assert lhs.getSort().isNumericSort();
		final CCTerm ccLhs = mClausifier.getCCTerm(lhs);
		final CCTerm ccRhs = mClausifier.getCCTerm(rhs);
		assert ccLhs != null && ccRhs != null;
		final DPLLAtom eqAtom = getLiteral(null);
		LAEquality laeq;
		if (eqAtom instanceof CCEquality) {
			final CCEquality eq = (CCEquality) eqAtom;
			laeq = eq.getLASharedData();
			if (laeq == null) {
				final Rational normFactor = computeNormFactor(mLhs, mRhs);
				laeq = createLAEquality();
				laeq.addDependentAtom(eq);
				eq.setLASharedData(laeq, normFactor);
			}
		} else {
			laeq = (LAEquality) eqAtom;
		}
		for (final CCEquality eq : laeq.getDependentEqualities()) {
			assert (eq.getLASharedData() == laeq);
			if (eq.getLhs() == ccLhs && eq.getRhs() == ccRhs) {
				return eq;
			}
			if (eq.getRhs() == ccLhs && eq.getLhs() == ccRhs) {
				return eq;
			}
		}
		final CCEquality eq = mClausifier.getCClosure().createCCEquality(mClausifier.getStackLevel(), ccLhs, ccRhs);
		final Rational normFactor = computeNormFactor(lhs, rhs);
		laeq.addDependentAtom(eq);
		eq.setLASharedData(laeq, normFactor);
		return eq;
	}

	private DPLLAtom createAtom(final Term eqTerm, final SourceAnnotation source) {
		mClausifier.addTermAxioms(mLhs, source);
		mClausifier.addTermAxioms(mRhs, source);

		final CCTerm lhsCCTerm = mClausifier.getCCTerm(mLhs);
		final CCTerm rhsCCTerm = mClausifier.getCCTerm(mRhs);
		boolean hasLhsLA = mClausifier.getLATerm(mLhs) != null;
		boolean hasRhsLA = mClausifier.getLATerm(mRhs) != null;
		if (lhsCCTerm == null && rhsCCTerm == null) {
			/* if both terms do not exist in CClosure yet, it may be better to
			 * create them in linear arithmetic.
			 * Do this, if we don't have a CClosure, or the other term is
			 * already in linear arithmetic.
			 */
			if ((mClausifier.getCClosure() == null || hasLhsLA) && !hasRhsLA) {
				mClausifier.createLinVar(mRhs, source);
				hasRhsLA = true;
			}
			if ((mClausifier.getCClosure() == null || hasRhsLA) && !hasLhsLA) {
				mClausifier.createLinVar(mLhs, source);
				hasLhsLA = true;
			}
		}

		/* Get linear arithmetic info, if both are arithmetic */
		if (hasLhsLA && hasRhsLA) {
			return createLAEquality();
		} else {
			/* let them share congruence closure */
			final CCTerm ccLhs = mClausifier.createCCTerm(mLhs, source);
			final CCTerm ccRhs = mClausifier.createCCTerm(mRhs, source);

			/* Creating the CC terms could have created the equality */
			final DPLLAtom atom = (DPLLAtom) mClausifier.getILiteral(eqTerm);
			if (atom != null) {
				return atom;
			}

			/* create CC equality */
			return mClausifier.getCClosure().createCCEquality(mClausifier.getStackLevel(), ccLhs, ccRhs);
		}
	}

	public DPLLAtom getLiteral(final SourceAnnotation source) {
		final Term eqTerm = mLhs.getTheory().term("=", mLhs, mRhs);
		DPLLAtom lit = (DPLLAtom) mClausifier.getILiteral(eqTerm);
		if (lit == null) {
			lit = createAtom(eqTerm, source);
			mClausifier.getLogger().debug("Created Equality: %s", lit);
			mClausifier.setTermFlags(eqTerm, mClausifier.getTermFlags(eqTerm)
					| Clausifier.POS_AUX_AXIOMS_ADDED
					| Clausifier.NEG_AUX_AXIOMS_ADDED);
			mClausifier.setLiteral(eqTerm, lit);
		}
		return lit;
	}

	@Override
	public String toString() {
		final PrintTerm pt = new PrintTerm();
		final StringBuilder sb = new StringBuilder();
		pt.append(sb, mLhs);
		sb.append(" == ");
		pt.append(sb, mRhs);
		return sb.toString();
	}

}
