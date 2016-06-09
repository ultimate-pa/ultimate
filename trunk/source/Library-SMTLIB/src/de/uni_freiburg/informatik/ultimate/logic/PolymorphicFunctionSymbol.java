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
import java.util.HashMap;


public class PolymorphicFunctionSymbol extends FunctionSymbolFactory {
	
	private final Sort[] mTypeParams;
	private final Sort[] mParamSorts;
	private final Sort mResultSort;
	private final int  mFlags;
	
	PolymorphicFunctionSymbol(String name, Sort[] typeParams, Sort[] params, 
			Sort result, int flags) {
		super(name);
		mTypeParams = typeParams;
		mParamSorts = params;
		mResultSort = result;
		mFlags      = flags;
	}

	@Override
	public int getFlags(BigInteger[] indices, Sort[] paramSorts, Sort result) {
		return mFlags;
	}

	@Override
	public Sort getResultSort(
			BigInteger[] indices, Sort[] paramSorts, Sort result) {
		if (indices != null) {
			return null;
		}
		if (paramSorts.length != mParamSorts.length) {
			return null;
		}
		final HashMap<Sort,Sort> unifier = new HashMap<Sort, Sort>();
		for (int i = 0; i < paramSorts.length; i++) {
			if (!mParamSorts[i].unifySort(unifier, paramSorts[i])) {
				return null;
			}
		}
		if (result != null) { // NOPMD
			if (!mResultSort.unifySort(unifier, result.getRealSort())) {
				return null;
			}
			return result;
		} else {
			final Sort[] mapping = new Sort[mTypeParams.length];
			for (int i = 0; i < mTypeParams.length; i++) {
				mapping[i] = unifier.get(mTypeParams[i]);
				// check if there are still unresolved type parameters.
				if (mapping[i] == null) {
					return null;
				}
			}
			return mResultSort.mapSort(mapping);
		}
	}
}
