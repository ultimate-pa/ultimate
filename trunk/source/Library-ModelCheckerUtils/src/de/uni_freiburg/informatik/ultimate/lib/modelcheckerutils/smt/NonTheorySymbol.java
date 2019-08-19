/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Wrapper for non-theory SMT symbols. 
 * A non-theory symbol is either a TermVariable, a constant or a FunctionSymbol.
 * We need this class because there is no common superclass for these three 
 * classes.
 * @author Matthias Heizmann
 *
 */
public abstract class NonTheorySymbol<SYMBOL> {
	private final SYMBOL mSymbol;

	private NonTheorySymbol(SYMBOL symbol) {
		super();
		mSymbol = symbol;
	}

	public SYMBOL getSymbol() {
		return mSymbol;
	}

	@Override
	public final int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((mSymbol == null) ? 0 : mSymbol.hashCode());
		return result;
	}

	@Override
	public final boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final NonTheorySymbol other = (NonTheorySymbol) obj;
		if (mSymbol == null) {
			if (other.mSymbol != null) {
				return false;
			}
		} else if (!mSymbol.equals(other.mSymbol)) {
			return false;
		}
		return true;
	}
	
	
	
	@Override
	public final String toString() {
		return mSymbol.toString();
	}

	public static Set<NonTheorySymbol<?>> extractNonTheorySymbols(Term term) {
		return (new NonTheorySymbolFinder()).findNonTheorySymbols(term);
	}
	
	public static class Variable extends NonTheorySymbol<TermVariable> {
		public Variable(TermVariable tv) {
			super(tv);
		}
	}
	
	public static class Constant extends NonTheorySymbol<ApplicationTerm> {
		public Constant(ApplicationTerm constant) {
			super(constant);
			if (constant.getParameters().length > 0) {
				throw new IllegalArgumentException("this is no constant");
			}
			if (constant.getFunction().isIntern()) {
				throw new IllegalArgumentException("this is not a non-theory symbol");
			}
		}
	}
	
	public static class Function extends NonTheorySymbol<FunctionSymbol> {
		public Function(FunctionSymbol functionSymbol) {
			super(functionSymbol);
			if (functionSymbol.isIntern()) {
				throw new IllegalArgumentException("this is not a non-theory symbol");
			}
		}
	}
}


