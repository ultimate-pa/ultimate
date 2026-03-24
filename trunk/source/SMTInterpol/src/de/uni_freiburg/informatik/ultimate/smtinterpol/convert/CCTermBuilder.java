/*
 * Copyright (C) 2009-2026 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.util.ArrayDeque;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;

public class CCTermBuilder {
	/**
	 * The clausifier.
	 */
	private final Clausifier mClausifier;
	private final SourceAnnotation mSource;

	private final ArrayDeque<Operation> mOps = new ArrayDeque<>();
	private final ArrayDeque<CCTerm> mConverted = new ArrayDeque<>();

	public CCTermBuilder(Clausifier clausifier, final SourceAnnotation source) {
		mClausifier = clausifier;
		mSource = source;
	}

	public CCTerm convert(final Term t) {
		mOps.push(new BuildCCTerm(t));
		while (!mOps.isEmpty()) {
			mOps.pop().perform();
		}
		final CCTerm res = mConverted.pop();
		assert mConverted.isEmpty();
		return res;
	}

	private class BuildCCTerm implements Operation {
		private final Term mTerm;

		public BuildCCTerm(final Term term) {
			mTerm = term;
		}

		@Override
		public void perform() {
			CCTerm ccTerm = mClausifier.getCCTerm(mTerm);
			if (ccTerm != null) {
				mConverted.push(ccTerm);
			} else {
				final CClosure cclosure = mClausifier.getCClosure();
				if (Clausifier.needCCTerm(mTerm)) {
					final FunctionSymbol fs = ((ApplicationTerm) mTerm).getFunction();
					if (fs.isIntern() && fs.getName() == "select") {
						mClausifier.getArrayTheory().cleanCaches();
					}
					mOps.push(new SaveCCTerm(mTerm));
					final ApplicationTerm at = (ApplicationTerm) mTerm;
					final Term[] args = at.getParameters();
					for (int i = args.length - 1; i >= 0; --i) {
						mOps.push(new BuildCCAppTerm(i != args.length - 1));
						mOps.push(new BuildCCTerm(args[i]));
					}
					mConverted.push(cclosure.getFuncTerm(fs));
				} else {
					// We have an intern function symbol
					ccTerm = cclosure.createAnonTerm(mTerm);
					cclosure.addTerm(ccTerm, mTerm);
					mClausifier.shareCCTerm(mTerm, ccTerm);
					mClausifier.addTermAxioms(mTerm, mSource);
					mConverted.push(ccTerm);
				}
			}
		}
	}

	private class SaveCCTerm implements Operation {
		private final Term mTerm;

		public SaveCCTerm(final Term term) {
			mTerm = term;
		}

		@Override
		public void perform() {
			final CCTerm ccTerm = mConverted.peek();
			mClausifier.getCClosure().addTerm(ccTerm, mTerm);
			mClausifier.shareCCTerm(mTerm, ccTerm);
			mClausifier.addTermAxioms(mTerm, mSource);
		}
	}

	/**
	 * Helper class to build the intermediate CCAppTerms. Note that all these terms will be func terms.
	 *
	 * @author Juergen Christ
	 */
	private class BuildCCAppTerm implements Operation {
		private final boolean mIsFunc;

		public BuildCCAppTerm(final boolean isFunc) {
			mIsFunc = isFunc;
		}

		@Override
		public void perform() {
			final CCTerm arg = mConverted.pop();
			final CCTerm func = mConverted.pop();
			mConverted.push(mClausifier.getCClosure().createAppTerm(mIsFunc, func, arg, mSource));
		}
	}
}