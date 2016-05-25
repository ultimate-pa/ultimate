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
package de.uni_freiburg.informatik.ultimate.smtinterpol.util;

public class SymmetricPair<T> {
	T mFst, mSnd;
	public SymmetricPair(T f, T s) {
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
		if (o instanceof SymmetricPair<?>) {
			final SymmetricPair<?> p = (SymmetricPair<?>) o;
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
