/*
 * Copyright (C) 2016 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Yu-Wen Chen
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

/**
 * copy of SMTInterpol's symmetric pair
 * 
 * @author Yu-Wen Chen
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
public class VPDomainSymmetricPair<T> {
	T mFst, mSnd;

	public VPDomainSymmetricPair(final T f, final T s) {
		assert f != null && s != null;
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
	public boolean equals(final Object o) {
		if (o instanceof VPDomainSymmetricPair<?>) {
			final VPDomainSymmetricPair<?> p = (VPDomainSymmetricPair<?>) o;
			return mFst.equals(p.mFst) && mSnd.equals(p.mSnd) || mFst.equals(p.mSnd) && mSnd.equals(p.mFst);
		}
		return false;
	}

	@Override
	public String toString() {
		return "(" + mFst + "," + mSnd + ")";
	}

	public boolean contains(final T element) {
		return mFst.equals(element) || mSnd.equals(element);
	}

	public T getOther(final T element) {
		if (element.equals(mFst)) {
			return mSnd;
		} else if (element.equals(mSnd)) {
			return mFst;
		}
		assert false : "check for containment first!";
		return null;

	}
}
