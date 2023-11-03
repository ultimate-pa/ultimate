/*
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbolFactory;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.SortSymbol;

public class MatchRewriteFunctionFactory extends FunctionSymbolFactory {

	public MatchRewriteFunctionFactory() {
		super(ProofConstants.FN_MATCH);
	}

	@Override
	public Sort getResultSort(String[] indices, Sort[] paramSorts, Sort resultSort) {
		if (paramSorts.length < 2 || indices != null || resultSort != null) {
			return null;
		}
		final SortSymbol eqProofSort = paramSorts[0].getSortSymbol();
		if (!eqProofSort.isIntern() || ! eqProofSort.getName().equals(ProofConstants.SORT_EQPROOF)) {
			return null;
		}
		if (!(paramSorts[0].getArguments()[0].getSortSymbol() instanceof DataType)) {
			return null;
		}
		final Sort theSort = paramSorts[1];
		if (paramSorts[1].getSortSymbol() != eqProofSort) {
			return null;
		}
		for (int i = 2; i < paramSorts.length; i++) {
			if (paramSorts[i] != theSort) {
				return null;
			}
		}
		return theSort;
	}
}
