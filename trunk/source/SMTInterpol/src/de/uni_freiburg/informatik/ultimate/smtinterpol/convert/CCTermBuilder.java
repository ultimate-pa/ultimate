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
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCParameter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;

public class CCTermBuilder {
	/**
	 * The clausifier.
	 */
	private final Clausifier mClausifier;
	private final SourceAnnotation mSource;

	private final ArrayDeque<Operation> mOps = new ArrayDeque<>();
	/**
	 * The converted results as {@link CCParameter}s: the term that produced {@code mConverted.peek()} has value
	 * {@code peek().getCCTerm() + peek().getOffset()}. The offset carries the {@code +5} of an offset-free term like
	 * {@code x+5} up to the enclosing application, where it ends up in that argument's {@link CCParameter}. Offsets are
	 * {@link Rational#ZERO} (i.e. a bare {@link CCTerm}) unless offset equalities are enabled.
	 */
	private final ArrayDeque<CCParameter> mConverted = new ArrayDeque<>();

	public CCTermBuilder(Clausifier clausifier, final SourceAnnotation source) {
		mClausifier = clausifier;
		mSource = source;
	}

	private void pushResult(final CCParameter ccParam) {
		mConverted.push(ccParam);
	}

	public CCParameter convert(final Term t) {
		mOps.push(new BuildCCTerm(t));
		while (!mOps.isEmpty()) {
			mOps.pop().perform();
		}
		final CCParameter res = mConverted.pop();
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
			// mCCTerms is keyed by offset-free terms; probe (and below build) the offset-free part, then re-apply the
			// constant as the CCParameter's offset (zero when the term is already offset-free).
			final Term offsetFree = mClausifier.getOffsetFreeTerm(mTerm);
			final CCTerm ccTerm = mClausifier.getCCTerm(offsetFree);
			if (ccTerm != null) {
				pushResult(CCParameter.of(ccTerm, mClausifier.getTermConstant(mTerm)));
			} else {
				final CClosure cclosure = mClausifier.getCClosure();
				if (offsetFree != mTerm) {
					// Numeric term with a non-zero constant: build the offset-free CCTerm and remember the constant.
					mOps.push(new AddOffsetToTerm(mClausifier.getTermConstant(mTerm)));
					mOps.push(new BuildCCTerm(offsetFree));
				} else if (Clausifier.needCCTerm(mTerm) && ((ApplicationTerm) mTerm).getParameters().length > 0) {
					final FunctionSymbol fs = ((ApplicationTerm) mTerm).getFunction();
					if (fs.isIntern() && fs.getName() == "select") {
						mClausifier.getArrayTheory().cleanCaches();
					}
					final ApplicationTerm at = (ApplicationTerm) mTerm;
					final Term[] args = at.getParameters();
					mOps.push(new BuildCCAppTerm(at));
					for (int i = args.length - 1; i >= 0; --i) {
						mOps.push(new BuildCCTerm(args[i]));
					}
				} else {
					// We have an intern function symbol
					final CCTerm anonTerm = cclosure.createAnonTerm(mTerm);
					cclosure.addTerm(anonTerm, mTerm);
					mClausifier.shareCCTerm(mTerm, anonTerm);
					mClausifier.addTermAxioms(mTerm, mSource);
					pushResult(anonTerm);
				}
			}
		}
	}

	/**
	 * Adds an offset to the (already built) numeric CCTerm of its offset-free part,
	 * and pushes the CCParameter with the offset.
	 */
	private class AddOffsetToTerm implements Operation {
		private final Rational mOffset;

		public AddOffsetToTerm(final Rational offset) {
			mOffset = offset;
		}

		@Override
		public void perform() {
			final CCTerm offsetFreeParam = (CCTerm) mConverted.pop();
			pushResult(CCParameter.of(offsetFreeParam, mOffset));
		}
	}

	/**
	 * Helper class to build the intermediate CCAppTerms. Note that all these terms will be func terms.
	 *
	 * @author Juergen Christ
	 */
	private class BuildCCAppTerm implements Operation {
		private final ApplicationTerm mAppTerm;

		public BuildCCAppTerm(ApplicationTerm appTerm) {
			mAppTerm = appTerm;
		}

		@Override
		public void perform() {
			final CCParameter[] args = new CCParameter[mAppTerm.getParameters().length];
			for (int i = args.length - 1; i >= 0; i--) {
				args[i] = mConverted.pop();
			}
			assert mClausifier.getCCTerm(mAppTerm) == null;
			final CCTerm ccTerm =
					mClausifier.getCClosure().createAppTerm(mAppTerm.getFunction(), args, mSource);
			mClausifier.getCClosure().addTerm(ccTerm, mAppTerm);
			mClausifier.shareCCTerm(mAppTerm, ccTerm);
			mClausifier.addTermAxioms(mAppTerm, mSource);
			// the application term itself is not numeric-offset; its value is the application
			pushResult(ccTerm);
		}
	}
}