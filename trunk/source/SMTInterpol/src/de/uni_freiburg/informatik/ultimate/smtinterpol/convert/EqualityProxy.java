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
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier.CCTermBuilder;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffinTerm;

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

	private final class RemoveAtom extends Clausifier.TrailObject {

		@Override
		public void undo() {
			mEqAtom = null;
		}

	}

	final Clausifier mClausifier;
	final SharedTerm mLhs, mRhs;
	DPLLAtom mEqAtom;

	public EqualityProxy(final Clausifier clausifier, final SharedTerm lhs, final SharedTerm rhs) {
		mClausifier = clausifier;
		mLhs = lhs;
		mRhs = rhs;
	}

	public LAEquality createLAEquality() {
		/* create la part */
		final MutableAffinTerm at = mClausifier.createMutableAffinTerm(mLhs);
		at.add(Rational.MONE, mClausifier.createMutableAffinTerm(mRhs));
		return mClausifier.getLASolver().createEquality(at);
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
	public CCEquality createCCEquality(final SharedTerm lhs, final SharedTerm rhs) {
		assert lhs.mCCterm != null && rhs.mCCterm != null;
		LAEquality laeq;
		if (mEqAtom == null) {
			mEqAtom = laeq = createLAEquality();
			mClausifier.addToUndoTrail(new RemoveAtom());
		} else if (mEqAtom instanceof CCEquality) {
			final CCEquality eq = (CCEquality) mEqAtom;
			laeq = eq.getLASharedData();
			if (laeq == null) {
				final MutableAffinTerm at = mClausifier.createMutableAffinTerm(mLhs);
				at.add(Rational.MONE, mClausifier.createMutableAffinTerm(mRhs));
				final Rational normFactor = at.getGCD().inverse();
				laeq = createLAEquality();
				laeq.addDependentAtom(eq);
				eq.setLASharedData(laeq, normFactor);
			}
		} else {
			laeq = (LAEquality) mEqAtom;
		}
		for (final CCEquality eq : laeq.getDependentEqualities()) {
			assert (eq.getLASharedData() == laeq);
			if (eq.getLhs() == lhs.mCCterm && eq.getRhs() == rhs.mCCterm) {
				return eq;
			}
			if (eq.getRhs() == lhs.mCCterm && eq.getLhs() == rhs.mCCterm) {
				return eq;
			}
		}
		final CCEquality eq = mClausifier.getCClosure().createCCEquality(
		        mClausifier.getStackLevel(), lhs.mCCterm, rhs.mCCterm);
		final MutableAffinTerm at = mClausifier.createMutableAffinTerm(lhs);
		at.add(Rational.MONE, mClausifier.createMutableAffinTerm(rhs));
		final Rational normFactor = at.getGCD().inverse();
		laeq.addDependentAtom(eq);
		eq.setLASharedData(laeq, normFactor);
		return eq;
	}

	private DPLLAtom createAtom(final SourceAnnotation source) {
		if (mLhs.mCCterm == null && mRhs.mCCterm == null) {
			/* if both terms do not exist in CClosure yet, it may be better to
			 * create them in linear arithmetic.
			 * Do this, if we don't have a CClosure, or the other term is
			 * already in linear arithmetic.
			 */
			if (mClausifier.getCClosure() == null
					|| mLhs.mOffset != null && mRhs.mOffset == null) {
				//m_Clausifier.createMutableAffinTerm(mRhs);
				mRhs.shareWithLinAr();
			}
			if (mClausifier.getCClosure() == null
					|| mLhs.mOffset == null && mRhs.mOffset != null) {
				//m_Clausifier.createMutableAffinTerm(mLhs);
				mLhs.shareWithLinAr();
			}
		}

		if (mLhs.getSort() != mRhs.getSort()) {
			/* This can only happen in Logic LIRA, where one of the
			 * shared terms is integer and the other is real.
			 *
			 * In this case we need to create the equality in the LASolver
			 * to check for integral values for the integer part.
			 */
			return createLAEquality();
		}

		/* check if the shared terms share at least one theory. */
		if (!((mLhs.mCCterm != null && mRhs.mCCterm != null)
				|| (mLhs.mOffset != null && mRhs.mOffset != null))) {
			/* let them share congruence closure */
			final CCTermBuilder cc = mClausifier.new CCTermBuilder(source);
			cc.convert(mLhs.getTerm());
			cc.convert(mRhs.getTerm());
		}

		/* Get linear arithmetic info, if both are arithmetic */
		if (mLhs.mOffset != null && mRhs.mOffset != null) { // NOPMD
			return createLAEquality();
		} else {
			/* create CC equality */
			return mClausifier.getCClosure().createCCEquality(
					mClausifier.getStackLevel(), mLhs.mCCterm, mRhs.mCCterm);
		}
	}

	public DPLLAtom getLiteral(final SourceAnnotation source) {
		if (mEqAtom == null) {
			mEqAtom = createAtom(source);
			if (mClausifier.getLogger().isDebugEnabled()) {
				mClausifier.getLogger().debug("Created Equality: " + mEqAtom);
			}
		}
		return mEqAtom;
	}

	@Override
	public String toString() {
		final PrintTerm pt = new PrintTerm();
		final StringBuilder sb = new StringBuilder();
		pt.append(sb, mLhs.getRealTerm());
		sb.append(" == ");
		pt.append(sb, mRhs.getRealTerm());
		return sb.toString();
	}

}
