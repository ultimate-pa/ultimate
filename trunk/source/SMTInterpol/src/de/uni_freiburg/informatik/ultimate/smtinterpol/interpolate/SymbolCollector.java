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
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet.UnletType;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

public class SymbolCollector extends TermTransformer {

	private HashMap<FunctionSymbol, Integer> mSymbols;
	
	/**
	 * Collect all symbols occurring in a given formula.  Do not use the
	 * {@link TermTransformer#transform(Term)} method on this class. 
	 * @param input The given formula.
	 */
	public final Map<FunctionSymbol, Integer> collect(Term input) {
		final Map<FunctionSymbol, Integer> res = mSymbols = 
			new HashMap<FunctionSymbol, Integer>();
		final FormulaUnLet unletter = new FormulaUnLet(UnletType.EXPAND_DEFINITIONS);
		final Term t = unletter.unlet(input);
		transform(t);
		mSymbols = null;
		return res;
	}
	
	public void startCollectTheory() {
		mSymbols = new HashMap<FunctionSymbol, Integer>();
	}
	
	public Set<FunctionSymbol> getTheorySymbols() {
		final Set<FunctionSymbol> res = mSymbols.keySet();
		mSymbols = null;
		return res;
	}
	
	public void addGlobalSymbols(Term input) {
		assert mSymbols != null : "call startCollectTheory() first";
		transform(input);
	}
	
	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
		final FunctionSymbol fs = appTerm.getFunction();
		if (!fs.isIntern()) {
			final Integer old = mSymbols.get(fs);
			final int val = old == null ? 1 : old + 1;
			mSymbols.put(fs, val);
		}
		super.convertApplicationTerm(appTerm, newArgs);
	}

}
