/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CodeCheck plug-in.
 * 
 * The ULTIMATE CodeCheck plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CodeCheck plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CodeCheck plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CodeCheck plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CodeCheck plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.emptinesscheck;

import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class Pair<T,U> {
	private final T m_First;
	private U m_Second;
	
	public Pair(T e1, U e2) {
		m_First = e1;
		m_Second = e2;
	}
	
	public T getFirst() {
		return m_First;
	}
	
	public U getSecond() {
		return m_Second;
	}
	
	private boolean equals(Pair<T, U> pair2) {
		if (pair2.getFirst().equals(m_First)) {
			if (pair2.getSecond().equals(m_Second)) {
				return true;
			}
		}
		return false;
	}
	
	public boolean equals(Object pair2) {
		if (pair2 instanceof Pair<?,?>)
			return this.equals((Pair<T,U>) pair2);
		else 
			return false;
	}
	
	public int hashCode() {
		return HashUtils.hashJenkins(m_First.hashCode(), m_Second.hashCode());
    }
	
	public String toString() {
		return "(" + m_First + "," + m_Second + ")";
	}
}
