/*
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.ematching;

import java.util.Arrays;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;

/**
 * Code to find a function application for a given function symbol. Executing this code will install a trigger in the
 * CClosure such that all new function applications with this function symbol are noticed. The remaining code can be
 * executed for each new function application.
 * 
 * @author Tanja Schindler
 */
public class FindCode implements ICode {

	private final EMatching mEMatching;
	private final CClosure mCClosure;
	private final FunctionSymbol mFunc;
	private final int mOutRegIndex;
	private final ICode mRemainingCode;

	public FindCode(final EMatching eMatching, final CClosure cclosure, final FunctionSymbol func, int outRegIndex,
			final ICode remainingCode) {
		mEMatching = eMatching;
		mCClosure = cclosure;
		mFunc = func;
		mOutRegIndex = outRegIndex;
		mRemainingCode = remainingCode;
	}

	@Override
	public void execute(final CCTerm[] register, final int decisionLevel) {
		if (mFunc.getParameterSorts().length > 0) {
			mEMatching.installFindTrigger(mFunc, mOutRegIndex, mRemainingCode, register, decisionLevel);
		}
		final List<CCTerm> funcApps = mCClosure.getAllFuncApps(mFunc);
		for (final CCTerm cand : funcApps) {
			final CCTerm[] updatedReg = Arrays.copyOf(register, register.length);
			updatedReg[mOutRegIndex] = cand;
			mEMatching.addCode(mRemainingCode, updatedReg, decisionLevel > 0 ? decisionLevel : 0);
		}
	}

	@Override
	public String toString() {
		return "find(" + mFunc + ", r" + mOutRegIndex + ",\n" + mRemainingCode.toString() + ")";
	}

}
