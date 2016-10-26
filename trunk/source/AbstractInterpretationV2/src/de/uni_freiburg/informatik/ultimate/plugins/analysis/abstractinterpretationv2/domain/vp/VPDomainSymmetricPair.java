/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This is a copy of class SymmetricPair, which is part of SMTInterpol.
 *
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

public class VPDomainSymmetricPair<T> {
	T mFst, mSnd;
	public VPDomainSymmetricPair(T f, T s) {
		mFst = f;
		mSnd = s;
	}
	
	public T getFirst() {
		return mFst;
	}
	public T getSecond() {
		return mSnd;
	}
	
	@Override
	public int hashCode() {
		return mFst.hashCode() + mSnd.hashCode();
	}

	@Override
	public boolean equals(Object o) {
		if (o instanceof VPDomainSymmetricPair<?>) {
			final VPDomainSymmetricPair<?> p = (VPDomainSymmetricPair<?>) o;
			return (mFst.equals(p.mFst) && mSnd.equals(p.mSnd))
			    || (mFst.equals(p.mSnd) && mSnd.equals(p.mFst));
		}
		return false;
	}
	
	@Override
	public String toString() {
		return "(" + mFst + "," + mSnd + ")";
	}
}
