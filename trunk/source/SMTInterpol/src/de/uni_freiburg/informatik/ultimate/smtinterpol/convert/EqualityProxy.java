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
			super(null, null, null, null);
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
			super(null, null, null, null);
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
	/** The offset-free sides and the constant offset: this proxy states {@code value(mLhs) == value(mRhs) + mOffset}. */
	final Term mLhs, mRhs;
	final Rational mOffset;

	public EqualityProxy(final Clausifier clausifier, final Term lhs, final Term rhs, final Rational offset) {
		mClausifier = clausifier;
		mLhs = lhs;
		mRhs = rhs;
		mOffset = offset;
	}

	public LAEquality createLAEquality() {
		// The proxy's canonical equality as a linear constraint: mLhs - mRhs - mOffset == 0.
		final Polynomial affine = new Polynomial(mLhs);
		affine.add(Rational.MONE, mRhs);
		affine.add(mOffset.negate());
		return mClausifier.getLASolver().createEquality(mClausifier.createMutableAffinTerm(affine, null));
	}

	/**
	 * The norm factor for a CCEquality between {@code lhs} and {@code rhs}: it relates the CCEquality to the proxy's
	 * shared LAEquality via {@code factor * (lhs - rhs) == laeq.getVar()}. It is per CCEquality, not per proxy, since
	 * equivalent equalities can be scaled (e.g. {@code 2x = 2y+4} vs {@code x = y+2} share a proxy but need factors 1/2
	 * and 1). The constant offset does not affect the gcd, so it is irrelevant here.
	 */
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
		// Resolve the offset-free CC nodes and the offset (the difference of the sides' constants); both are per call,
		// not the proxy's, since this lhs/rhs may be a scaled equivalent of the proxy's canonical equality.
		return createCCEquality(mClausifier.getCCTerm(mClausifier.getOffsetFreeTerm(lhs)),
				mClausifier.getCCTerm(mClausifier.getOffsetFreeTerm(rhs)),
				mClausifier.getTermConstant(rhs).sub(mClausifier.getTermConstant(lhs)));
	}

	/**
	 * Create a CCEquality {@code value(ccLhs) == value(ccRhs) + offset} linked to this proxy's LAEquality. The offset
	 * and norm factor are derived from {@code ccLhs}/{@code ccRhs}/{@code offset} (not from the proxy's canonical
	 * {@link #mOffset}), because equivalent equalities can be scaled and share this proxy at different offsets.
	 */
	public CCEquality createCCEquality(final CCTerm ccLhs, final CCTerm ccRhs, final Rational offset) {
		assert ccLhs != null && ccRhs != null;
		final DPLLAtom eqAtom = getLiteral(SourceAnnotation.EMPTY_SOURCE_ANNOT);
		LAEquality laeq;
		if (eqAtom instanceof CCEquality) {
			final CCEquality eq = (CCEquality) eqAtom;
			laeq = eq.getLASharedData();
			if (laeq == null) {
				laeq = createLAEquality();
				laeq.addDependentAtom(eq);
				eq.setLASharedData(laeq, computeNormFactor(eq.getLhs().getFlatTerm(), eq.getRhs().getFlatTerm()));
			}
		} else {
			laeq = (LAEquality) eqAtom;
		}
		for (final CCEquality eq : laeq.getDependentEqualities()) {
			assert (eq.getLASharedData() == laeq);
			// The offset must match too: two CCEqualities between the same pair of CCTerms but with different offsets
			// (e.g. x == y and x == y + 3) are distinct facts and must not be conflated, otherwise propagating one
			// would wrongly set the other. eq states getLhs() == getRhs() + eq.getOffset().
			if (eq.getLhs() == ccLhs && eq.getRhs() == ccRhs && eq.getOffset().equals(offset)) {
				return eq;
			}
			if (eq.getLhs() == ccRhs && eq.getRhs() == ccLhs && eq.getOffset().equals(offset.negate())) {
				return eq;
			}
		}
		final CCEquality eq =
				mClausifier.getCClosure().createCCEquality(mClausifier.getStackLevel(), ccLhs, ccRhs, offset);
		laeq.addDependentAtom(eq);
		eq.setLASharedData(laeq, computeNormFactor(ccLhs.getFlatTerm(), ccRhs.getFlatTerm()));
		return eq;
	}

	private DPLLAtom createAtom(final Term eqTerm, final SourceAnnotation source) {
		// mLhs/mRhs are offset-free, so axioms, existence probes and LinVar creation operate directly on them; the
		// offset (mOffset) is reintroduced when the CCEquality is built below.
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
			final CCTerm ccLhs = mClausifier.createCCTerm(mLhs, source).getCCTerm();
			final CCTerm ccRhs = mClausifier.createCCTerm(mRhs, source).getCCTerm();

			/* Creating the CC terms could have created the equality */
			final DPLLAtom atom = (DPLLAtom) mClausifier.getILiteral(eqTerm);
			if (atom != null) {
				return atom;
			}

			/* create CC equality */
			final CCEquality cceq =
					mClausifier.getCClosure().createCCEquality(mClausifier.getStackLevel(), ccLhs, ccRhs, mOffset);
			if (mClausifier.createOffsetEqualities() && mLhs.getSort().isNumericSort()) {
				// With offset equalities, clash-slot MBTC only creates LAEqualities for shared terms that occupy a
				// function-argument position; a numeric (dis)equality between other shared terms (e.g. two selector or
				// div results) would otherwise have no LAEquality, so linear arithmetic would never learn the
				// disequality and model construction could pick a model that violates it. Create the LAEquality eagerly
				// (it forces the necessary LinVars, here both sides are numeric) and link it to the CCEquality, exactly
				// as createCCEquality does once a term is already shared.
				final LAEquality laeq = createLAEquality();
				laeq.addDependentAtom(cceq);
				cceq.setLASharedData(laeq, computeNormFactor(mLhs, mRhs));
			}
			return cceq;
		}
	}

	public DPLLAtom getLiteral(final SourceAnnotation source) {
		// Reconstruct the offset-aware equality term (mLhs == mRhs + mOffset) as the literal/flag key, so proxies that
		// differ only by their offset get distinct atoms (mirrors CCEquality.getSMTFormula).
		final Term rhsWithOffset =
				mOffset.equals(Rational.ZERO) ? mRhs : mClausifier.addConstantToTerm(mRhs, mOffset);
		final Term eqTerm = mLhs.getTheory().term("=", mLhs, rhsWithOffset);
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
		if (!mOffset.equals(Rational.ZERO)) {
			sb.append(" + ").append(mOffset);
		}
		return sb.toString();
	}

}
