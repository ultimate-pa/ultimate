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
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;

public class CCBaseTerm extends CCTerm {
	Object symbol;
	
	public CCBaseTerm(boolean isFunc, int parentPos, Object symb, SharedTerm term) {
		super(isFunc, parentPos, term, symb.hashCode());
		this.symbol = symb;
	}

	/**
	 * Create a CCBaseTerm that is not part of the e-graph and is only used for interpolation.
	 * @param symb
	 */
	public CCBaseTerm(Object symb) {
		super();
		this.symbol = symb;
	}
	
	public Term toSMTTerm(Theory t, boolean useAuxVars)
	{
		assert !isFunc;
		if (symbol instanceof SharedTerm)
			return ((SharedTerm) symbol).getRealTerm();// TODO auxvar stuff
		assert symbol instanceof FunctionSymbol;
		FunctionSymbol func = (FunctionSymbol) symbol;
		assert func.getParameterCount() == 0;
		return t.term(func);
	}

	public String toString() {
		if (symbol instanceof FunctionSymbol)
			return ((FunctionSymbol)symbol).getName();
		return symbol.toString();
	}

	public FunctionSymbol getFunctionSymbol() {
		return (FunctionSymbol) symbol;
	}
	
	public boolean isFunctionSymbol() {
		return symbol instanceof FunctionSymbol;
	}
}
