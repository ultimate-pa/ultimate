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
package de.uni_freiburg.informatik.ultimate.logic;

import java.math.BigInteger;
import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.util.datastructures.UnifyHash;

/**
 * Factory for overloaded and/or polymorphic function symbols.
 * @author hoenicke
 */
public abstract class FunctionSymbolFactory {
	String mFuncName;
	UnifyHash<FunctionSymbol> mInstances;
	
	public FunctionSymbolFactory(String name) {
		mFuncName = name;
		mInstances = new UnifyHash<FunctionSymbol>();
	}

	public abstract Sort getResultSort(
			BigInteger[] indices, Sort[] paramSorts, Sort resultSort);

	public int getFlags(BigInteger[] indices, Sort[] paramSorts, Sort result) {
		return FunctionSymbol.INTERNAL;
	}

	private static boolean isReal(Sort[] sorts) {
		for (final Sort s : sorts) {
			if (s.getRealSort() != s) {
				return false;
			}
		}
		return true;
	}
	
	public Term getDefinition(TermVariable[] tvs, Sort resultSort) { // NOPMD
		return null;
	}
	
	public FunctionSymbol getFunctionWithResult(
			Theory theory, BigInteger[] indices, Sort[] paramSorts,
			Sort resultSort) {
		assert isReal(paramSorts);
		final int flags = getFlags(indices, paramSorts, resultSort);
		if ((flags & (FunctionSymbol.ASSOCMASK)) != 0) {
			if (paramSorts.length < 2) {
				return null;
			}
			final Sort[] realParams = new Sort[] {
				paramSorts[0], paramSorts[paramSorts.length - 1]
			};
			final Sort otherSort = 
				(flags & (FunctionSymbol.ASSOCMASK)) == FunctionSymbol.LEFTASSOC
				? realParams[1] : realParams[0];
			for (int i = 1; i < paramSorts.length - 1; i++) {
				if (paramSorts[i] != otherSort) {
					return null;
				}
			}
			paramSorts = realParams;
		}
		if (((flags & (FunctionSymbol.RETURNOVERLOAD)) == 0)
				!= (resultSort == null)) {
			/* According to standard the return type must be given
			 * if and only if the function is overloaded on the return type. 
			 */
			return null;
		}
		final int hash = Arrays.hashCode(indices)
			^ Arrays.hashCode(paramSorts) 
			^ (resultSort == null ? 0 : resultSort.hashCode());
		for (final FunctionSymbol func : mInstances.iterateHashCode(hash)) {
			if (Arrays.equals(func.mIndices, indices)
				&& Arrays.equals(func.mParamSort, paramSorts)
				&& (resultSort == null
						|| func.mReturnSort == resultSort)) {
				return func;
			}
		}
		
		resultSort = getResultSort(indices, paramSorts, resultSort); 
		if (resultSort == null) {
			return null;
		}
		
		TermVariable[] defVars = new TermVariable[paramSorts.length];
		for (int i = 0; i < paramSorts.length; i++) {
			defVars[i] = theory.createTermVariable("x" + i, paramSorts[i]);
		}
		Term definition;
		if (((flags & (FunctionSymbol.RETURNOVERLOAD)) != 0)// NOPMD
			&& resultSort != resultSort.getRealSort()) {
			final FunctionSymbol realFunc = 
				getFunctionWithResult(theory, indices, paramSorts,
						resultSort.getRealSort());
			definition = theory.term(realFunc, defVars);
		} else {
			definition = getDefinition(defVars, resultSort);
		}
		if (definition == null) {
			defVars = null;
		}
		final FunctionSymbol func = new FunctionSymbol(
				mFuncName, indices, paramSorts, resultSort, 
					defVars, definition, flags); 
		mInstances.put(hash, func);
		return func;
	}
	
	@Override
	public String toString() {
		return mFuncName;
	}
}
