/*
 * Copyright (C) 2021 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAnnotation.RuleKind;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * This ReverseTrigger is meant to be applied on to constructor terms and trigger the execution of rule 1 & 2 of the data type theory
 *
 * @author moritz
 *
 */
public class DTReverseTrigger extends ReverseTrigger {
	/**
	 * The constructor term on which this trigger is applied.
	 */
	final CCTerm mArg;

	int mArgPos;

	/**
	 * The function symbol on which this trigger will be activated.
	 */
	final FunctionSymbol mFunctionSymbol;
	final Clausifier mClausifier;
	final DataTypeTheory mDTTheory;

	public DTReverseTrigger(final DataTypeTheory dtTheory, final Clausifier clausifier, final FunctionSymbol fs, final CCTerm arg) {
		mDTTheory = dtTheory;
		mClausifier = clausifier;
		mFunctionSymbol = fs;
		mArg = arg;
	}

	@Override
	public CCTerm getArgument() {
		return mArg;
	}

	@Override
	public int getArgPosition() {
		return 0;
	}

	@Override
	public FunctionSymbol getFunctionSymbol() {
		return mFunctionSymbol;
	}

	@SuppressWarnings("unchecked")
	@Override
	public void activate(final CCAppTerm appTerm, final boolean isFresh) {
		mClausifier.getLogger().debug("DTReverseTrigger: %s on %s", appTerm, mArg);
		final ApplicationTerm argAT = (ApplicationTerm) mArg.mFlatTerm;
		final SymmetricPair<CCTerm>[] reason;
		if (appTerm.getArg() != mArg) {
			reason = new SymmetricPair[] {
				new SymmetricPair<>(appTerm.getArg(), mArg)
			};
		} else {
			reason = new SymmetricPair[0];
		}
		if (mFunctionSymbol.getName() == "is") {
			// If appTerm is a "is" function, check if it tests for the constructor of mArg.
			// If so set the function equal to true else to false.
			final FunctionSymbol fs = ((CCBaseTerm)appTerm.mFunc).getFunctionSymbol();
			final Term truthValue;
			if (fs.getIndices()[0].equals(argAT.getFunction().getName())) {
				truthValue = mClausifier.getTheory().mTrue;
			} else {
				truthValue = mClausifier.getTheory().mFalse;
			}
			final SymmetricPair<CCTerm> mainEq = new SymmetricPair<>(appTerm, mClausifier.getCCTerm(truthValue));
			final DataTypeLemma lemma = new DataTypeLemma(RuleKind.DT_TESTER, mainEq, reason, mArg);
			mDTTheory.addPendingLemma(lemma);
			if (isFresh) {
				mDTTheory.addRecheckOnBacktrack(appTerm);
			}
		} else {
			// If appTerm is a selector function, set it equal to the matching argument of mArg.
			final FunctionSymbol fs = argAT.getFunction();
			final DataType argDT = (DataType) fs.getReturnSort().getSortSymbol();
			final Constructor c = argDT.getConstructor(argAT.getFunction().getName());
			for (int i = 0; i < c.getSelectors().length; i++) {
				if (mFunctionSymbol.getName() == c.getSelectors()[i]) {
					final SymmetricPair<CCTerm> mainEq = new SymmetricPair<>(appTerm,
							mClausifier.getCCTerm(argAT.getParameters()[i]));
					final DataTypeLemma lemma = new DataTypeLemma(RuleKind.DT_PROJECT, mainEq, reason, mArg);
					mDTTheory.addPendingLemma(lemma);
					if (isFresh) {
						mDTTheory.addRecheckOnBacktrack(appTerm);
					}
					return;
				}
			}

			throw new AssertionError("selector function not part of constructor");
		}
	}

}
