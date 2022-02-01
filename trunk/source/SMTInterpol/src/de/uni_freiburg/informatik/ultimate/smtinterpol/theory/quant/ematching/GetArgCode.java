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

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAppTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;

/**
 * Code to get the specified argument of the candidate for a specified term.
 * 
 * @author Tanja Schindler
 */
public class GetArgCode implements ICode {

	private final EMatching mEMatching;
	private final int mAppTermRegIndex, mOutRegIndex;
	private final FunctionSymbol mFunc;
	private final int mArgPos;
	private final ICode mRemainingCode;

	public GetArgCode(final EMatching eMatching, final int appTermRegIndex, final FunctionSymbol func, final int argPos,
			final int outRegIndex, final ICode remainingCode) {
		mEMatching = eMatching;
		mAppTermRegIndex = appTermRegIndex;
		mFunc = func;
		mArgPos = argPos;
		mOutRegIndex = outRegIndex;
		mRemainingCode = remainingCode;
	}

	@Override
	public void execute(final CCTerm[] register, final int decisionLevel) {
		final CCTerm appTerm = register[mAppTermRegIndex];
		assert appTerm instanceof CCAppTerm;
		CCAppTerm partialApp = (CCAppTerm) appTerm;
		for (int i = 0; i < mFunc.getParameterSorts().length - mArgPos - 1; i++) {
			partialApp = (CCAppTerm) ((CCAppTerm) partialApp).getFunc();
		}
		final CCTerm arg = partialApp.getArg();
		final CCTerm[] updatedRegister = Arrays.copyOf(register, register.length);
		updatedRegister[mOutRegIndex] = arg;
		mEMatching.addCode(mRemainingCode, updatedRegister, decisionLevel);
	}

	@Override
	public String toString() {
		return "getArg(r" + mAppTermRegIndex + ", " + mFunc + ", " + mArgPos + ", r" + mOutRegIndex + ",\n"
				+ mRemainingCode.toString() + ")";
	}

}
