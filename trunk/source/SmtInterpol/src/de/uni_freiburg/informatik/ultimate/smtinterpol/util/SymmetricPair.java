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
	T fst, snd;
	public SymmetricPair(T f, T s) {
		fst = f;
		snd = s;
	}
	
	public T getFirst() {
		return fst;
	}
	public T getSecond() {
		return snd;
	}
	
	public int hashCode() {
		return fst.hashCode() + snd.hashCode();
	}

	public boolean equals(Object o) {
		if (o instanceof SymmetricPair<?>) {
			SymmetricPair<?> p = (SymmetricPair<?>) o;
			return (fst.equals(p.fst) && snd.equals(p.snd))
			    || (fst.equals(p.snd) && snd.equals(p.fst));
		}
		return false;
	}
	
	public String toString() {
		return "("+fst+","+snd+")";
	}
}
