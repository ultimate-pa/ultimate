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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;

public class CCBaseTerm extends CCTerm {
	Object mSymbol;
	
	public CCBaseTerm(boolean isFunc, int parentPos, Object symb, SharedTerm term) {
		super(isFunc, parentPos, term, symb.hashCode());
		mSymbol = symb;
	}

	@Override
	public String toString() {
		if (mSymbol instanceof FunctionSymbol) {
			return ((FunctionSymbol)mSymbol).getName();
		}
		return mSymbol.toString();
	}

	public FunctionSymbol getFunctionSymbol() {
		return (FunctionSymbol) mSymbol;
	}
	
	public boolean isFunctionSymbol() {
		return mSymbol instanceof FunctionSymbol;
	}
}
