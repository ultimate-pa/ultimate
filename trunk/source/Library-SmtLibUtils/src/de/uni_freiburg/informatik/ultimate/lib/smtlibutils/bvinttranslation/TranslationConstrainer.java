/*
 * Copyright (C) 2021-2022 Max Barth (Max.Barth95@gmx.de)
 * Copyright (C) 2021-2022 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.bvinttranslation;

import java.math.BigInteger;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.UnfTransformer;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class TranslationConstrainer {
	private final ManagedScript mMgdScript;
	private final Script mScript;
	private FunctionSymbol mIntand;

	public enum ConstraintsForBitwiseOperations {
		/**
		 * Precise "sum" constraints for bit-wise-and
		 */
		SUM,
		/**
		 * Precise "bit-wise" constraints for bit-wise-and
		 */
		BITWISE,
		/**
		 * Overapproximation of bit-wise-and by lazy constraints
		 */
		LAZY,
		/**
		 * Overapproximation of all bit-wise functions by auxiliary variables
		 */
		NONE
		/**
		 * Overapproximation of all bit-wise functions by uninterpreted function
		 * symbol
		 */
	}

	public final ConstraintsForBitwiseOperations mMode;

	private final HashSet<Term> mConstraintSet; // Set of all constraints
	private final HashSet<Term> mTvConstraintSet; // Set of all constraints for
													// quantified variables
	private final HashSet<Term> mBvandConstraintSet; // Only the constraints for
														// bvand for congruence
														// based translation
	/*
	 * This Class contains of the methods to create constraints for the
	 * translation of bit-wise-AND and variables. The constraints for
	 * uninterpreted constants and bit-wise-AND can be accessed via
	 * getConstraints(). The constraints for TermVariables can be accessed via
	 * getTvConstraints().
	 */

	public TranslationConstrainer(final ManagedScript mgdscript, final ConstraintsForBitwiseOperations mode) {
		mMgdScript = mgdscript;
		mScript = mgdscript.getScript();
		mMode = mode;

		mConstraintSet = new HashSet<Term>();
		mBvandConstraintSet = new HashSet<Term>();
		mTvConstraintSet = new HashSet<Term>();
		// mTranslatedTerms = new HashMap<>();
		// mReversedTranslationMap = new HashMap<>();

		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		final Sort[] functionsort = new Sort[2];
		functionsort[0] = intSort;
		functionsort[1] = intSort;

		if (mIntand == null) {
			if (mScript.getFunctionSymbol("intand") == null) {
				mScript.declareFun("intand", functionsort, intSort);
			}
			mIntand = mScript.getFunctionSymbol("intand");
		}
	}

	// returns the Set of constraints for uninterpreted constants and
	// bit-wise-AND
	public HashSet<Term> getConstraints() {
		return mConstraintSet;
	}

	public HashSet<Term> getBvandConstraints() {
		return mBvandConstraintSet;
	}

	// returns the Set of constraints for TermVariables
	public HashSet<Term> getTvConstraints() {
		return mTvConstraintSet;
	}

	public FunctionSymbol getIntAndFunctionSymbol() {
		return mIntand;
	}

	private Term getLowerVarBounds(final Term bvterm, final Term intTerm) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		final Term translatedVar = intTerm;
		final Term lowerBound = mScript.term("<=", Rational.ZERO.toTerm(intSort), translatedVar);
		return lowerBound;
	}

	private Term getUpperVarBounds(final Term bvterm, final Term intTerm) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		final int width = Integer.valueOf(bvterm.getSort().getIndices()[0]);

		final Term translatedVar = intTerm;
		final Rational twoPowWidth = Rational.valueOf(BigInteger.valueOf(2).pow(width), BigInteger.ONE);
		final Rational twoPowWidthSubOne = twoPowWidth.sub(Rational.ONE);
		// Strict upper Bound
		final Term upperBoundPaper =
				mScript.term("<", translatedVar, SmtUtils.rational2Term(mScript, twoPowWidth, intSort));
		final Term upperBound =
				mScript.term("<=", translatedVar, SmtUtils.rational2Term(mScript, twoPowWidthSubOne, intSort));
		return upperBoundPaper;
	}

	public void varConstraint(final Term bvterm, final Term intTerm) {
		mConstraintSet.add(getLowerVarBounds(bvterm, intTerm));
		mConstraintSet.add(getUpperVarBounds(bvterm, intTerm));
	}

	public Term getTvConstraint(final TermVariable bvterm, final Term intTerm) {
		final Term lowerBound = getLowerVarBounds(bvterm, intTerm);
		final Term upperBoundPaper = getUpperVarBounds(bvterm, intTerm);
		mTvConstraintSet.add(lowerBound);
		mTvConstraintSet.add(upperBoundPaper);
		return mScript.term("and", lowerBound, upperBoundPaper);
	}

	// returns bounds for select terms, they are not added to the sets.
	public Term getSelectConstraint(final Term bvterm, final Term intTerm) {
		final Term lowerBound = getLowerVarBounds(bvterm, intTerm);
		final Term upperBoundPaper = getUpperVarBounds(bvterm, intTerm);
		return mScript.term("and", lowerBound, upperBoundPaper);
	}

	/**
	 *
	 * @return true iff the constraints define only an overapproximation of
	 *         bvand.
	 */
	public boolean bvandConstraint(final Term intTerm, final int width) {
		if (mMode.equals(ConstraintsForBitwiseOperations.NONE)) {
			return true;
		}
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		if (!SmtSortUtils.isIntSort(intTerm.getSort())) {
			throw new UnsupportedOperationException("Cannot create Constraints vor non-Int Sort Terms");
		}
		if (intTerm instanceof ApplicationTerm) {
			final ApplicationTerm apterm = (ApplicationTerm) intTerm;
			final Term translatedLHS = apterm.getParameters()[0];
			final Term translatedRHS = apterm.getParameters()[1];

			final Rational twoPowWidth = Rational.valueOf(BigInteger.valueOf(2).pow(width), BigInteger.ONE);

			final Term modeConstraint;
			Term lazy = mScript.term("true");
			switch (mMode) {
			case SUM: {
				final Term lowerBound = mScript.term("<=", Rational.ZERO.toTerm(intSort), apterm);
				final Term upperBound =
						mScript.term("<", apterm, SmtUtils.rational2Term(mScript, twoPowWidth, intSort));
				mBvandConstraintSet.add(lowerBound);
				mBvandConstraintSet.add(upperBound);
				modeConstraint = bvandSUMConstraints(width, translatedLHS, translatedRHS);
				break;
			}
			case BITWISE: {
				final Term lowerBound = mScript.term("<=", Rational.ZERO.toTerm(intSort), apterm);
				final Term upperBound =
						mScript.term("<", apterm, SmtUtils.rational2Term(mScript, twoPowWidth, intSort));
				mConstraintSet.add(lowerBound);
				mConstraintSet.add(upperBound);
				mBvandConstraintSet.add(lowerBound);
				mBvandConstraintSet.add(upperBound);
				modeConstraint = bvandBITWISEConstraints(width, translatedLHS, translatedRHS);
				break;
			}
			case LAZY: {
				final Term lowerBound = mScript.term("<=", Rational.ZERO.toTerm(intSort), apterm);
				final Term upperBound =
						mScript.term("<", apterm, SmtUtils.rational2Term(mScript, twoPowWidth, intSort));
				lazy = bvandLAZYConstraints(width, translatedLHS, translatedRHS);
				mConstraintSet.add(lowerBound);
				mConstraintSet.add(upperBound);
				mConstraintSet.add(lazy);

				mBvandConstraintSet.add(lowerBound);
				mBvandConstraintSet.add(upperBound);
				mBvandConstraintSet.add(lazy);
				return true;
			}

			case NONE: {
				throw new UnsupportedOperationException("Deal with this mode at the beginning of this method");
			}
			default: {
				throw new UnsupportedOperationException("Set Mode for bvand Constraints");
			}
			}

			// Important, to match with the backtranslation we also need to
			// bring it in the
			// same form here
			final UnfTransformer unfT = new UnfTransformer(mScript);
			final Term unfModeConstraint = unfT.transform(modeConstraint);
			mConstraintSet.add(unfModeConstraint);
			mBvandConstraintSet.add(unfModeConstraint);
			return false;
		}
		throw new AssertionError("method must be called on IntAnd");
	}

	private Term bvandSUMConstraints(final int width, final Term translatedLHS, final Term translatedRHS) {
		final Term sum = bvandSUMforReplacement(width, translatedLHS, translatedRHS);
		if (width == 1) {
			return SmtUtils.binaryEquality(mScript, mScript.term(mIntand.getName(), translatedLHS, translatedRHS), sum);

		} else {
			return SmtUtils.binaryEquality(mScript, mScript.term(mIntand.getName(), translatedLHS, translatedRHS), sum);
		}
	}

	public Term bvandSUMforReplacement(final int width, final Term translatedLHS, final Term translatedRHS) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		final BigInteger two = BigInteger.valueOf(2);
		final Term[] sum = new Term[width];
		for (int i = 0; i < width; i++) { // width + 1?
			final Term twoPowI = SmtUtils.rational2Term(mScript, Rational.valueOf(two.pow(i), BigInteger.ONE), intSort);
			final Term one = SmtUtils.rational2Term(mScript, Rational.ONE, intSort);
			final Term zero = SmtUtils.rational2Term(mScript, Rational.ZERO, intSort);
			final Term ite = mScript.term("ite", mScript.term("=", isel(i, translatedLHS), isel(i, translatedRHS), one),
					one, zero);
			final Term mul = mScript.term("*", twoPowI, ite);
			sum[i] = mul;
		}
		if (width == 1) {
			return sum[0];

		} else {
			return mScript.term("+", sum);
		}
	}

	private Term bvandBITWISEConstraints(final int width, final Term translatedLHS, final Term translatedRHS) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		final Term[] and = new Term[width];
		for (int i = 0; i < width; i++) {
			final Term one = SmtUtils.rational2Term(mScript, Rational.ONE, intSort);
			final Term zero = SmtUtils.rational2Term(mScript, Rational.ZERO, intSort);
			final Term ite = mScript.term("ite", mScript.term("=", isel(i, translatedLHS), isel(i, translatedRHS), one),
					one, zero);
			final Term equals =
					mScript.term("=", isel(i, mScript.term(mIntand.getName(), translatedLHS, translatedRHS)), ite);
			and[i] = equals;
		}
		return SmtUtils.and(mScript, and);
	}

	private Term bvandLAZYConstraints(final int width, final Term translatedLHS, final Term translatedRHS) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		final Term zero = SmtUtils.rational2Term(mScript, Rational.ZERO, intSort);
		final Term maxNumber = SmtUtils.rational2Term(mScript,
				Rational.valueOf(BigInteger.valueOf(2).pow(width), BigInteger.ONE), intSort);
		final Term[] lazyConstraints = new Term[8];
		final Term intand = mScript.term(mIntand.getName(), translatedLHS, translatedRHS);
		// LHS upper Bound
		lazyConstraints[0] = mScript.term("<=", intand, translatedLHS);
		// RHS upper Bound
		lazyConstraints[1] = mScript.term("<=", intand, translatedRHS);
		// Idempotence
		lazyConstraints[2] = mScript.term("=>", mScript.term("=", translatedLHS, translatedRHS),
				mScript.term("=", intand, translatedLHS));
		// Symmetry
		lazyConstraints[3] = mScript.term("=", intand, mScript.term(mIntand.getName(), translatedRHS, translatedLHS));
		// LHS Zero
		lazyConstraints[4] =
				mScript.term("=>", mScript.term("=", translatedLHS, zero), mScript.term("=", intand, zero));
		// RHS Zero
		lazyConstraints[5] =
				mScript.term("=>", mScript.term("=", zero, translatedRHS), mScript.term("=", intand, zero));
		// LHS max number
		lazyConstraints[6] = mScript.term("=>", mScript.term("=", translatedLHS, maxNumber),
				mScript.term("=", intand, translatedRHS));
		// RHS max number
		lazyConstraints[7] = mScript.term("=>", mScript.term("=", maxNumber, translatedRHS),
				mScript.term("=", intand, translatedLHS));
		return mScript.term("and", lazyConstraints);
	}

	// Term that picks the bit at position "i" of integer term "term"
	// interpreted as
	// binary
	private Term isel(final int i, final Term term) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		final Term two =
				SmtUtils.rational2Term(mScript, Rational.valueOf(BigInteger.valueOf(2), BigInteger.ONE), intSort);
		final Term twoPowI = SmtUtils.rational2Term(mScript,
				Rational.valueOf(BigInteger.valueOf(2).pow(i), BigInteger.ONE), intSort);
		return mScript.term("mod", mScript.term("div", term, twoPowI), two);
	}
}
