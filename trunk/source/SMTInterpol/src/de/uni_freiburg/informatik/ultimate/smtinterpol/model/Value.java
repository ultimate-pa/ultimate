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
package de.uni_freiburg.informatik.ultimate.smtinterpol.model;

import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class Value implements ExecTerm {

	private final Term mVal;
	
	public Value(Term val) {
		mVal = val;
	}
	
	@Override
	public ExecTerm evaluate(ExecTerm... args) {
		return this;
	}

	@Override
	public Term toSMTLIB(Theory t, TermVariable[] vars) {
		return mVal;
	}
	
	public int hashCode() {
		return mVal.hashCode();
	}
	
	public boolean equals(Object other) {
		if (other instanceof Value) {
			Value o = (Value) other;
			if (mVal instanceof ConstantTerm && o.mVal instanceof ConstantTerm)
				return ((ConstantTerm) mVal).getValue().equals(
						((ConstantTerm) o.mVal).getValue());
			return mVal == ((Value) other).mVal;
		}
		return false;
	}

	@Override
	public boolean isUndefined() {
		return false;
	}

}
