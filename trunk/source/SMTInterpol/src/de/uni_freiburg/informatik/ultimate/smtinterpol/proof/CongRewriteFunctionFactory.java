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

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbolFactory;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.SortSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class CongRewriteFunctionFactory extends FunctionSymbolFactory {

	public CongRewriteFunctionFactory() {
		super(ProofConstants.FN_CONG);
	}

	public static FunctionSymbol getFunctionFromIndex(String[] indices, Sort[] paramSorts, Sort resultSort) {
		if (paramSorts.length == 0 || indices == null) {
			return null;
		}
		final Theory theory = paramSorts[0].getTheory();
		final SortSymbol eqProofSort = paramSorts[0].getSortSymbol();
		if (!eqProofSort.isIntern() || ! eqProofSort.getName().equals(ProofConstants.SORT_EQPROOF)) {
			return null;
		}
		String[] origIndices;
		if (indices.length > 1) {
			origIndices = new String[indices.length - 1];
			System.arraycopy(indices, 1, origIndices, 0, indices.length - 1);
		} else {
			origIndices = null;
		}
		final Sort[] origParamSorts = new Sort[paramSorts.length];
		for (int i = 0; i < paramSorts.length; i++) {
			if (paramSorts[i].getSortSymbol() != eqProofSort) {
				return null;
			}
			origParamSorts[i] = paramSorts[i].getArguments()[0];
		}
		Sort origResultSort;
		if (resultSort == null) {
			origResultSort = null;
		} else {
			if (resultSort.getSortSymbol() != eqProofSort) {
				return null;
			}
			origResultSort = resultSort.getArguments()[0];
		}
		return theory.getFunctionWithResult(indices[0], origIndices, origResultSort, origParamSorts);
	}

	@Override
	public int getFlags(String[] indices, Sort[] paramSorts, Sort resultSort) {
		final FunctionSymbol func = getFunctionFromIndex(indices, paramSorts, resultSort);
		if (func != null) {
			return (func.isLeftAssoc() ? FunctionSymbol.LEFTASSOC : 0)
					| (func.isRightAssoc() ? FunctionSymbol.RIGHTASSOC : 0)
					| (func.isReturnOverload() ? FunctionSymbol.RETURNOVERLOAD : 0) | FunctionSymbol.INTERNAL;
		}
		return FunctionSymbol.INTERNAL;
	}

	@Override
	public Sort getResultSort(String[] indices, Sort[] paramSorts, Sort resultSort) {
		final FunctionSymbol origFunc = getFunctionFromIndex(indices, paramSorts, resultSort);
		if (origFunc == null) {
			return null;
		}
		final SortSymbol eqProofSort = paramSorts[0].getSortSymbol();
		return eqProofSort.getSort(null, new Sort[] { origFunc.getReturnSort() });
	}

}
