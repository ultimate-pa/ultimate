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
	
	private final Sort[] m_TypeParams;
	private final Sort[] m_ParamSorts;
	private final Sort m_ResultSort;
	private final int  m_Flags;
	
	PolymorphicFunctionSymbol(String name, Sort[] typeParams, Sort[] params, 
			Sort result, int flags) {
		super(name);
		m_TypeParams = typeParams;
		m_ParamSorts = params;
		m_ResultSort = result;
		m_Flags      = flags;
	}

	public int getFlags(BigInteger[] indices, Sort[] paramSorts, Sort result) {
		return m_Flags;
	}

	public Sort getResultSort
		(BigInteger[] indices, Sort[] paramSorts, Sort result) {
		if (indices != null)
			return null;
		if (paramSorts.length != m_ParamSorts.length)
			return null;
		HashMap<Sort,Sort> unifier = new HashMap<Sort, Sort>();
		for (int i = 0; i < paramSorts.length; i++) {
			if (!m_ParamSorts[i].unifySort(unifier, paramSorts[i]))
				return null;
		}
		if (result != null) {
			if (!m_ResultSort.unifySort(unifier, result.getRealSort()))
				return null;
			return result;
		} else {
			Sort[] mapping = new Sort[m_TypeParams.length];
			for (int i = 0; i < m_TypeParams.length; i++) {
				mapping[i] = unifier.get(m_TypeParams[i]);
				// check if there are still unresolved type parameters.
				if (mapping[i] == null)
					return null;
			}
			return m_ResultSort.mapSort(mapping);
		}
	}
}
