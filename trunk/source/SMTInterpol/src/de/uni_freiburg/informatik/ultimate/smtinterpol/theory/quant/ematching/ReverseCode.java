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

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCParameter;

/**
 * Code to find a function application for a given function symbol that has the given term as argument at the given
 * position. Executing this code will install a trigger in the CClosure such that all new function applications with
 * these properties are noticed. The remaining code can be executed for each new function application.
 * 
 * @author Tanja Schindler
 */
public class ReverseCode implements ICode {

	private final EMatching mEMatching;

	private final int mArgRegIndex;
	private final FunctionSymbol mFunc;
	private final int mArgPos;
	private final int mOutRegIndex;
	private final ICode mRemainingCode;

	public ReverseCode(final EMatching eMatching, final int argRegIndex, final FunctionSymbol func, final int argPos,
			final int outRegIndex, final ICode remainingCode) {
		mEMatching = eMatching;
		mArgRegIndex = argRegIndex;
		mFunc = func;
		mArgPos = argPos;
		mOutRegIndex = outRegIndex;
		mRemainingCode = remainingCode;
	}

	@Override
	public void execute(final CCParameter[] register, final int decisionLevel) {
		final CCParameter arg = register[mArgRegIndex];
		mEMatching.installReverseTrigger(mFunc, arg, mArgPos, mOutRegIndex, mRemainingCode, register, decisionLevel);
	}

	@Override
	public String toString() {
		return "reverse(" + mFunc + ", " + mArgPos + ", r" + mArgRegIndex + ", r" + mOutRegIndex + ",\n"
				+ mRemainingCode.toString() + ")";
	}

}
