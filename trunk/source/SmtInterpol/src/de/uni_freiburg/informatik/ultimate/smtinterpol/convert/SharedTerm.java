/*
 * Copyright (C) 2009-2012 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinVar;

public class SharedTerm {
	
	private final Clausifier mClausifier;
	private final Term mTerm;
	private final IAnnotation mAnnot;
	
	// fields for theory.cclosure (Congruence Closure)
	CCTerm mCCterm;
	
	// fields for theory.linar (Linear Arithmetic)
	LinVar mLinVar;
	Rational mFactor, mOffset;
	
	private Term mRealTerm = null;
	
	public SharedTerm(Clausifier clausifier, Term term) {
		mClausifier = clausifier;
		mTerm = term;
		if (clausifier.getEngine().isProofGenerationEnabled())
			mAnnot = mClausifier.getAnnotation();
		else
			mAnnot = null;
	}
	
	public void setLinVar(Rational factor, LinVar linvar, Rational offset) {
		mFactor = factor;
		mLinVar = linvar;
		mOffset = offset;
	}
	
	public void share() {
		if (mClausifier.getLogger().isInfoEnabled())
			mClausifier.getLogger().info("Sharing term: " + this);
		assert (mCCterm != null && mOffset != null);
		mClausifier.getLASolver().share(this);
		mCCterm.share(mClausifier.getCClosure(), this);
	}
		
	public void shareWithLinAr() {
		if (mOffset != null)
			return;
		assert getSort().isNumericSort() : "Sharing non-numeric sort?";
		
		if (mTerm instanceof SMTAffineTerm) {
			mClausifier.getLASolver().generateSharedVar(
					this, mClausifier.createMutableAffinTerm(
							(SMTAffineTerm) mTerm),
					mClausifier.getStackLevel());
		} else {
			boolean isint = getSort().getName().equals("Int");
			mLinVar = mClausifier.getLASolver().addVar(this, isint,
					mClausifier.getStackLevel());
			
			mFactor = Rational.ONE;
			mOffset = Rational.ZERO;
		}
		mClausifier.addUnshareLA(this);
		if (mCCterm != null)
			share();
	}
	
	public EqualityProxy createEquality(SharedTerm other) {
		SharedTerm a = this, b = other;
		if (getSort() != other.getSort()) {
			// LIRA: convert both terms to reals.
			if (getSort().getName().equals("Real")) {
				b = mClausifier.toReal(b);
			} else {
				a = mClausifier.toReal(a);
			}
		}
		return mClausifier.createEqualityProxy(a, b);
	}

	public void unshareLA() {
		mFactor = null;
		mLinVar = null;
		mOffset = null;
	}
	
	public void unshareCC() {
		mCCterm = null;
	}

	public LinVar getLinVar() {
		return mLinVar;
	}
	public Rational getOffset() {
		return mOffset;
	}
	public Rational getFactor() {
		return mFactor;
	}

	public boolean validShared() {
		return mCCterm != null && mOffset != null;
	}
	
	public Sort getSort() {
		return mTerm.getSort();
	}

	public Term getTerm() {
		return mTerm;
	}
	/**
	 * Get a term that can be used outside of SMTInterpol.  The result is equal
	 * to {@link #getTerm()} unless this function returns a
	 * {@link SMTAffineTerm}.  In this case, the result equals the application
	 * of {@link SMTAffineTerm#cleanup(Term)} applied to {@link #getTerm()}.
	 * @return A cleaned up term.
	 */
	public Term getRealTerm() {
		if (mRealTerm == null)
			mRealTerm = SMTAffineTerm.cleanup(mTerm);
		return mRealTerm;
	}
	
	public IAnnotation getAnnotation() {
		return mAnnot;
	}
	
	public Clausifier getClausifier() {
		return mClausifier;
	}

	public CCTerm getCCTerm() {
		return mCCterm;
	}
	
	public int hashCode() {
		return mTerm.hashCode();
	}
	
	public String toString() {
		return SMTAffineTerm.cleanup(mTerm).toString();
	}
	
	void setCCTerm(CCTerm ccterm) {
		assert(mCCterm == null);
		mCCterm = ccterm;
		mClausifier.addUnshareCC(this);
		if (mOffset != null)
			share();
	}
}
