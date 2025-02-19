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
import java.util.LinkedHashMap;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.BitvectorUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.bvinttranslation.TranslationConstrainer.ConstraintsForBitwiseOperations;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class BvToIntTransferrer extends TermTransferrer {
	private final Script mScript;
	private final Script mBvScript;
	private static final String BITVEC_CONST_PATTERN = "bv\\d+";
	private final boolean mNutzTransformation;
	private final ManagedScript mMgdScript;
	private final TermVariable[] mFreeVars;
	private final TranslationConstrainer mTc;

	private final LinkedHashMap<Term, Term> mVariableMap; // Maps BV Var to
															// Integer Var
	private final LinkedHashMap<Term, Term> mReversedVarMap;
	public final LinkedHashMap<Term, Term> mArrayConstraintMap;
	private final Set<Term> mOverapproxVariables;
	private boolean mIsOverapproximation;

	// For statistics
	// Count in integer formula
	int utsCount = 0;
	int moduloCount = 0;
	// Count in Bv formula, dont count abbreviations
	int arithmeticBvCount = 0; // bv +,-,-,*,mod,div
	int bvandCount = 0;
	int shiftsCount = 0; // left and right shift
	int concatCount = 0; // zeroextend and concat
	int bvdivBvmodCount = 0; // bv div and mod
	/*
	 * Translates a formula over bit-vector to a formula over integers. Can
	 * translate arrays and quantifiers.
	 *
	 * Everything that works with pushTerm needs the BvScript and everything
	 * that works with SetResult needs the IntScript
	 */

	public BvToIntTransferrer(final Script oldScript, final Script newScript, final ManagedScript mgdscript,
			final LinkedHashMap<Term, Term> variableMap, final TranslationConstrainer tc, final TermVariable[] freeVars,
			final boolean useNutzTransformation) {
		super(oldScript, newScript);
		mMgdScript = mgdscript;
		mScript = newScript;
		mBvScript = oldScript;
		mNutzTransformation = useNutzTransformation;

		mFreeVars = freeVars;
		if (variableMap != null) {
			mVariableMap = variableMap;
		} else {
			mVariableMap = new LinkedHashMap<>();
		}

		mReversedVarMap = new LinkedHashMap<>();
		mArrayConstraintMap = new LinkedHashMap<>();
		mOverapproxVariables = new HashSet<>();
		mIsOverapproximation = false;
		mTc = tc;
	}

	@Override
	public void convert(final Term term) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		if (term instanceof TermVariable) {
			for (final TermVariable variable : mFreeVars) {
				if (term == variable && SmtSortUtils.isBitvecSort(term.getSort())) {
					final Term intVar = translateVars(term, true);
					assert (SmtSortUtils.isIntSort(intVar.getSort()));
					mTc.varConstraint(term, intVar); // Create and Collect
														// Constraints
					setResult(intVar);
					return;
				}
			}
			setResult(translateVars(term, true));
			return;
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;

			final FunctionSymbol fsym = appTerm.getFunction();
			if (appTerm.getParameters().length == 0) {
				if (SmtUtils.isConstant(appTerm)) {
					final Term intVar = translateVars(term, true);
					if (SmtSortUtils.isBitvecSort(term.getSort())) {
						mTc.varConstraint(term, intVar); // Create and Collect
															// Constraints
					}
					setResult(intVar);
					return;
				}
			}
			// NONE Overapproximation
			if (mTc.mMode.equals(ConstraintsForBitwiseOperations.NONE) && overaproxWithVars(appTerm)) {
				final Sort newSort = IntBlastingWrapper.translateSort(mScript, appTerm.getSort());
				final TermVariable overaproxVar = mMgdScript.constructFreshTermVariable("overaproxVar", newSort);
				final Term overaproxConst = SmtUtils.termVariable2constant(mScript, overaproxVar, true);
				mOverapproxVariables.add(overaproxConst);
				mIsOverapproximation = true;
				setResult(overaproxConst);
				return;
			}

			if (fsym.isIntern()) {
				switch (fsym.getName()) {
				case "bvor": {
					// bvor = bvsub(bvadd, bvand)
					final Term bvor = BitvectorUtils.unfTerm(mBvScript, "bvsub", null,
							BitvectorUtils.unfTerm(mBvScript, "bvadd", null, appTerm.getParameters()),
							BitvectorUtils.unfTerm(mBvScript, "bvand", null, appTerm.getParameters()));
					pushTerm(bvor);
					return;
				}
				case "bvxor": {
					final Term bvxor = BitvectorUtils.unfTerm(mBvScript, "bvsub", null,
							BitvectorUtils.unfTerm(mBvScript, "bvsub", null,
									BitvectorUtils.unfTerm(mBvScript, "bvadd", null, appTerm.getParameters()),
									BitvectorUtils.unfTerm(mBvScript, "bvand", null, appTerm.getParameters())),
							BitvectorUtils.unfTerm(mBvScript, "bvand", null, appTerm.getParameters()));
					pushTerm(bvxor);
					return;
				}
				case "bvashr": {
					pushTerm(bvashrAbbreviation(appTerm));
					return;
				}
				case "sign_extend": {
					pushTerm(signextendAbbreviation(appTerm));
					return;
				}
				case "bvsrem": {
					pushTerm(bvsremAbbreviation(appTerm));
					return;
				}

				case "bvsdiv": {
					pushTerm(bvsdivAbbreviation(appTerm));
					return;
				}
				case "bvxnor": {
					pushTerm(bvxnorAbbreviation(appTerm));
					return;
				}
				case "bvnand": {
					pushTerm(bvnandAbbreviation(appTerm));
					return;
				}
				// TODO BitvectorUtils doesnt support rotate
				// case "bvcomp": {
				// pushTerm(bvcompAbbreviation(appTerm));
				// return;
				// }
				case "bvsmod": {
					pushTerm(bvsmodAbbreviation(appTerm));
					return;
				}
				// TODO BitvectorUtils doesnt support rotate
				// case "rotate_left": {
				// pushTerm(rotateLeftAbbreviation(appTerm));
				// return;
				// }
				// TODO BitvectorUtils doesnt support rotate
				// case "rotate_right": {
				// pushTerm(rotateRightAbbreviation(appTerm));
				// return;
				// }
				}
			}
		} else if (term instanceof ConstantTerm)

		{
			if (SmtSortUtils.isBitvecSort(term.getSort())) {
				final ConstantTerm constTerm = (ConstantTerm) term;
				assert isBitVecSort(constTerm.getSort());
				BigInteger constValue;
				if (constTerm.getValue() instanceof String) {
					String bitString = (String) constTerm.getValue();
					if (bitString.startsWith("#b")) {
						bitString = (String) constTerm.getValue();
						constValue = new BigInteger(bitString.substring(2), 2);
					} else if (bitString.startsWith("#x")) {
						constValue = new BigInteger(bitString.substring(2), 16);
					} else {
						throw new UnsupportedOperationException("Unexpected constant type");
					}
				} else {
					constValue = (BigInteger) constTerm.getValue();
				}
				final Term intConst =
						SmtUtils.rational2Term(mScript, Rational.valueOf(constValue, BigInteger.ONE), intSort);

				setResult(intConst);
				return;
			} else {
				throw new UnsupportedOperationException("unexpected constant sort");
			}
		}
		super.convert(term);

	}

	private Term bvashrAbbreviation(final ApplicationTerm appTerm) {
		final BigInteger[] indices = new BigInteger[2];
		indices[0] = BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 1);
		indices[1] = BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 1);
		final Term zeroVec =
				SmtUtils.rational2Term(mBvScript, Rational.ZERO, SmtSortUtils.getBitvectorSort(mBvScript, 1));
		final Term extract = BitvectorUtils.unfTerm(mBvScript, "extract", indices, appTerm.getParameters()[0]);

		final Term ifTerm = SmtUtils.binaryEquality(mBvScript, extract, zeroVec);

		final Term thenTerm = BitvectorUtils.unfTerm(mBvScript, "bvlshr", null, appTerm.getParameters());

		final Term elseTerm = BitvectorUtils.unfTerm(mBvScript, "bvnot", null,
				BitvectorUtils.unfTerm(mBvScript, "bvlshr", null,
						BitvectorUtils.unfTerm(mBvScript, "bvnot", null, appTerm.getParameters()[0]),
						appTerm.getParameters()[1]));

		final Term ite = SmtUtils.ite(mBvScript, ifTerm, thenTerm, elseTerm);
		return ite;
	}

	private Term bvxnorAbbreviation(final ApplicationTerm appTerm) {
		final Term bvxnor = BitvectorUtils.unfTerm(mBvScript, "bvor", null,
				BitvectorUtils.unfTerm(mBvScript, "bvor", null,
						BitvectorUtils.unfTerm(mBvScript, "bvand", null, appTerm.getParameters()),
						BitvectorUtils.unfTerm(mBvScript, "bvand", null,
								BitvectorUtils.unfTerm(mBvScript, "bvnot", null, appTerm.getParameters()[0]),
								BitvectorUtils.unfTerm(mBvScript, "bvnot", null, appTerm.getParameters()[1]))));
		return bvxnor;
	}

	private Term bvnandAbbreviation(final ApplicationTerm appTerm) {
		final Term bvnand = BitvectorUtils.unfTerm(mBvScript, "bvnot", null,
				BitvectorUtils.unfTerm(mBvScript, "bvand", null, appTerm.getParameters()));
		return bvnand;
	}

	private Term bvcompAbbreviation(final ApplicationTerm appTerm) {
		final Term bvcomp;
		final int width = Integer.valueOf(appTerm.getSort().getIndices()[0]);
		if (width == 1) { // width = 1
			final Term bvxnor = BitvectorUtils.unfTerm(mBvScript, "bvxnor", null, appTerm.getParameters());
			bvcomp = bvxnor;
		} else {
			final BigInteger[] indices = new BigInteger[2];
			indices[0] = BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 1);
			indices[1] = BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 1);
			final Term msbLhs = BitvectorUtils.unfTerm(mBvScript, "extract", indices, appTerm.getParameters()[0]);
			final Term msbRhs = BitvectorUtils.unfTerm(mBvScript, "extract", indices, appTerm.getParameters()[1]);

			final BigInteger[] indicesRest = new BigInteger[2];
			indicesRest[0] =
					BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 2);
			indicesRest[1] = BigInteger.ZERO;
			final Term extractRest = BitvectorUtils.unfTerm(mBvScript, "extract", indices, appTerm.getParameters()[0]);

			final Term bvxnor = BitvectorUtils.unfTerm(mBvScript, "bvxnor", null, msbLhs, msbRhs);
			final Term bvcompRest = BitvectorUtils.unfTerm(mBvScript, "bvcomp", null, extractRest);
			final Term bvand = BitvectorUtils.unfTerm(mBvScript, "bvxnor", null, bvxnor, bvcompRest);
			bvcomp = bvand;
		}

		return bvcomp;
	}

	private Term bvsmodAbbreviation(final ApplicationTerm appTerm) {
		final BigInteger[] indices = new BigInteger[2];
		indices[0] = BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 1);
		indices[1] = BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 1);
		final Term msbLhs = BitvectorUtils.unfTerm(mBvScript, "extract", indices, appTerm.getParameters()[0]);
		final Term msbRhs = BitvectorUtils.unfTerm(mBvScript, "extract", indices, appTerm.getParameters()[1]);

		final Term zeroVec =
				SmtUtils.rational2Term(mBvScript, Rational.ZERO, SmtSortUtils.getBitvectorSort(mBvScript, 1));
		final Term oneVec =
				SmtUtils.rational2Term(mBvScript, Rational.ONE, SmtSortUtils.getBitvectorSort(mBvScript, 1));

		final Term mbsLhsEqualsZero = SmtUtils.equality(mBvScript, zeroVec, msbLhs);
		final Term mbsRhsEqualsZero = SmtUtils.equality(mBvScript, zeroVec, msbRhs);
		final Term mbsLhsEqualsOne = SmtUtils.equality(mBvScript, oneVec, msbLhs);
		final Term mbsRhsEqualsOne = SmtUtils.equality(mBvScript, oneVec, msbRhs);

		final Term absLhs = SmtUtils.ite(mBvScript, mbsLhsEqualsZero, appTerm.getParameters()[0],
				BitvectorUtils.unfTerm(mBvScript, "bvneg", null, appTerm.getParameters()[0]));
		final Term absRhs = SmtUtils.ite(mBvScript, mbsRhsEqualsZero, appTerm.getParameters()[1],
				BitvectorUtils.unfTerm(mBvScript, "bvneg", null, appTerm.getParameters()[1]));

		final Term bvurem = BitvectorUtils.unfTerm(mBvScript, "bvurem", null, absLhs, absRhs);

		final int width = Integer.valueOf(appTerm.getSort().getIndices()[0]);
		final Term zeroVecOfWidth =
				SmtUtils.rational2Term(mBvScript, Rational.ZERO, SmtSortUtils.getBitvectorSort(mBvScript, width));

		final Term ifTerm1 = SmtUtils.equality(mBvScript, bvurem, zeroVecOfWidth);

		final Term ifTerm2 = SmtUtils.and(mBvScript, mbsLhsEqualsZero, mbsRhsEqualsZero);

		final Term ifTerm3 = SmtUtils.and(mBvScript, mbsLhsEqualsOne, mbsRhsEqualsZero);

		final Term ifTerm4 = SmtUtils.and(mBvScript, mbsLhsEqualsZero, mbsRhsEqualsOne);

		final Term thenTerm3 = BitvectorUtils.unfTerm(mBvScript, "bvadd", null,
				BitvectorUtils.unfTerm(mBvScript, "bvneg", null, bvurem), appTerm.getParameters()[1]);

		final Term thenTerm4 = BitvectorUtils.unfTerm(mBvScript, "bvadd", null, appTerm.getParameters()[0],
				appTerm.getParameters()[1]);

		final Term elseTerm = BitvectorUtils.unfTerm(mBvScript, "bvneg", null, bvurem);

		final Term ite4 = SmtUtils.ite(mBvScript, ifTerm4, thenTerm4, elseTerm);
		final Term ite3 = SmtUtils.ite(mBvScript, ifTerm3, thenTerm3, ite4);
		final Term ite2 = SmtUtils.ite(mBvScript, ifTerm2, bvurem, ite3);
		final Term ite1 = SmtUtils.ite(mBvScript, ifTerm1, bvurem, ite2);
		final Term bvsmod = ite1;
		return bvsmod;
	}

	// TODO BitvectorUtils doesnt support rotate
	private Term rotateLeftAbbreviation(final ApplicationTerm appTerm) {
		final Term rotateL;
		final int width = Integer.valueOf(appTerm.getSort().getIndices()[0]);
		if (width == 1) { // width = 1
			rotateL = appTerm.getParameters()[0];
		} else {
			final BigInteger[] indices = new BigInteger[2];
			indices[0] = BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 2);
			indices[1] = BigInteger.ZERO;
			final BigInteger[] indicesMSB = new BigInteger[2];
			indicesMSB[0] =
					BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 1);
			indicesMSB[1] =
					BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 1);
			final BigInteger[] rotateRest = new BigInteger[1];
			rotateRest[0] = BigInteger.valueOf(width - 1);
			rotateL = BitvectorUtils.unfTerm(mBvScript, "rotate_left", rotateRest,

					BitvectorUtils.unfTerm(mBvScript, "concat", null,
							BitvectorUtils.unfTerm(mBvScript, "extract", indices, appTerm.getParameters()[0]),
							BitvectorUtils.unfTerm(mBvScript, "extract", indicesMSB, appTerm.getParameters()[0])));

		}

		return rotateL;
	}

	// TODO BitvectorUtils doesnt support rotate
	private Term rotateRightAbbreviation(final ApplicationTerm appTerm) {
		final Term rotateR;
		final int width = Integer.valueOf(appTerm.getSort().getIndices()[0]);
		if (width == 1) { // width = 1
			rotateR = appTerm.getParameters()[0];
		} else {
			final BigInteger[] indices = new BigInteger[2];
			indices[0] = BigInteger.ZERO;
			indices[1] = BigInteger.ZERO;
			final BigInteger[] indicesMSB = new BigInteger[2];
			indicesMSB[0] =
					BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 1);
			indicesMSB[1] = BigInteger.ONE;
			final BigInteger[] rotateRest = new BigInteger[1];
			rotateRest[0] = BigInteger.valueOf(width - 1);
			rotateR = BitvectorUtils.unfTerm(mBvScript, "rotate_right", rotateRest,

					BitvectorUtils.unfTerm(mBvScript, "concat", null,
							BitvectorUtils.unfTerm(mBvScript, "extract", indices, appTerm.getParameters()[0]),
							BitvectorUtils.unfTerm(mBvScript, "extract", indicesMSB, appTerm.getParameters()[0])));

		}

		return rotateR;
	}

	private Term signextendAbbreviation(final ApplicationTerm appTerm) {
		final BigInteger[] indices = new BigInteger[2];
		indices[0] = BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 1);
		indices[1] = BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 1);

		Term repeat = appTerm.getParameters()[0];
		final int difference = Integer.valueOf(appTerm.getSort().getIndices()[0])
				- Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]);
		for (int i = 0; i < difference; i++) {
			repeat = BitvectorUtils.unfTerm(mBvScript, "concat", null,
					BitvectorUtils.unfTerm(mBvScript, "extract", indices, appTerm.getParameters()[0]), repeat);
		}
		return repeat;
	}

	/*
	 * This method gets as input an application term with function symbol bvsrem
	 * and returns the definition of bvsrem.
	 */
	private Term bvsremAbbreviation(final ApplicationTerm appTerm) {
		final BigInteger[] indices = new BigInteger[2];
		indices[0] = BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 1);
		indices[1] = BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 1);
		final Term msbLhs = BitvectorUtils.unfTerm(mBvScript, "extract", indices, appTerm.getParameters()[0]);
		final Term msbRhs = BitvectorUtils.unfTerm(mBvScript, "extract", indices, appTerm.getParameters()[1]);

		final Term zeroVec =
				SmtUtils.rational2Term(mBvScript, Rational.ZERO, SmtSortUtils.getBitvectorSort(mBvScript, 1));
		final Term oneVec =
				SmtUtils.rational2Term(mBvScript, Rational.ONE, SmtSortUtils.getBitvectorSort(mBvScript, 1));
		final Term ifterm1 = SmtUtils.and(mBvScript, SmtUtils.equality(mBvScript, zeroVec, msbLhs),
				SmtUtils.equality(mBvScript, zeroVec, msbRhs));
		final Term ifterm2 = SmtUtils.and(mBvScript, SmtUtils.equality(mBvScript, oneVec, msbLhs),
				SmtUtils.equality(mBvScript, zeroVec, msbRhs));
		final Term ifterm3 = SmtUtils.and(mBvScript, SmtUtils.equality(mBvScript, zeroVec, msbLhs),
				SmtUtils.equality(mBvScript, oneVec, msbRhs));

		final Term bvurem = BitvectorUtils.unfTerm(mBvScript, "bvurem", null, appTerm.getParameters());
		final Term thenTerm2 = BitvectorUtils.unfTerm(mBvScript, "bvneg", null,
				BitvectorUtils.unfTerm(mBvScript, "bvurem", null,
						BitvectorUtils.unfTerm(mBvScript, "bvneg", null, appTerm.getParameters()[0]),
						appTerm.getParameters()[1]));
		final Term thenTerm3 = BitvectorUtils.unfTerm(mBvScript, "bvneg", null,
				BitvectorUtils.unfTerm(mBvScript, "bvurem", null, appTerm.getParameters()[0],
						BitvectorUtils.unfTerm(mBvScript, "bvneg", null, appTerm.getParameters()[1])));

		final Term elseTerm = BitvectorUtils.unfTerm(mBvScript, "bvneg", null,
				BitvectorUtils.unfTerm(mBvScript, "bvurem", null,
						BitvectorUtils.unfTerm(mBvScript, "bvneg", null, appTerm.getParameters()[0]),
						BitvectorUtils.unfTerm(mBvScript, "bvneg", null, appTerm.getParameters()[1])));

		final Term iteChain2 = SmtUtils.ite(mBvScript, ifterm3, thenTerm3, elseTerm);
		final Term iteChain1 = SmtUtils.ite(mBvScript, ifterm2, thenTerm2, iteChain2);
		final Term bvsrem = SmtUtils.ite(mBvScript, ifterm1, bvurem, iteChain1);
		return bvsrem;

	}

	/*
	 * This method gets as input an application term with function symbol bvsdiv
	 * and returns the definition of bvsdiv.
	 */
	private Term bvsdivAbbreviation(final ApplicationTerm appTerm) {
		final BigInteger[] indices = new BigInteger[2];
		indices[0] = BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 1);
		indices[1] = BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 1);
		final Term msbLhs = BitvectorUtils.unfTerm(mBvScript, "extract", indices, appTerm.getParameters()[0]);
		final Term msbRhs = BitvectorUtils.unfTerm(mBvScript, "extract", indices, appTerm.getParameters()[1]);

		final Term zeroVec =
				SmtUtils.rational2Term(mBvScript, Rational.ZERO, SmtSortUtils.getBitvectorSort(mBvScript, 1));
		final Term oneVec =
				SmtUtils.rational2Term(mBvScript, Rational.ONE, SmtSortUtils.getBitvectorSort(mBvScript, 1));

		final Term ifterm1 = SmtUtils.and(mBvScript, SmtUtils.equality(mBvScript, zeroVec, msbLhs),
				SmtUtils.equality(mBvScript, zeroVec, msbRhs));
		final Term ifterm2 = SmtUtils.and(mBvScript, SmtUtils.equality(mBvScript, oneVec, msbLhs),
				SmtUtils.equality(mBvScript, zeroVec, msbRhs));
		final Term ifterm3 = SmtUtils.and(mBvScript, SmtUtils.equality(mBvScript, zeroVec, msbLhs),
				SmtUtils.equality(mBvScript, oneVec, msbRhs));

		final Term bvudiv = BitvectorUtils.unfTerm(mBvScript, "bvudiv", null, appTerm.getParameters());
		final Term thenTerm2 = BitvectorUtils.unfTerm(mBvScript, "bvneg", null,
				BitvectorUtils.unfTerm(mBvScript, "bvudiv", null,
						BitvectorUtils.unfTerm(mBvScript, "bvneg", null, appTerm.getParameters()[0]),
						appTerm.getParameters()[1]));
		final Term thenTerm3 = BitvectorUtils.unfTerm(mBvScript, "bvneg", null,
				BitvectorUtils.unfTerm(mBvScript, "bvudiv", null, appTerm.getParameters()[0],
						BitvectorUtils.unfTerm(mBvScript, "bvneg", null, appTerm.getParameters()[1])));

		final Term elseTerm = BitvectorUtils.unfTerm(mBvScript, "bvudiv", null,
				BitvectorUtils.unfTerm(mBvScript, "bvneg", null, appTerm.getParameters()[0]),
				BitvectorUtils.unfTerm(mBvScript, "bvneg", null, appTerm.getParameters()[1]));

		final Term iteChain2 = SmtUtils.ite(mBvScript, ifterm3, thenTerm3, elseTerm);
		final Term iteChain1 = SmtUtils.ite(mBvScript, ifterm2, thenTerm2, iteChain2);
		final Term bvsdiv = SmtUtils.ite(mBvScript, ifterm1, bvudiv, iteChain1);

		return bvsdiv;
	}

	/*
	 * Gets as Input an ArraySort, if domain Sort or range Sort is bit-vector
	 * the method returns a new array where this Sort is replaced by integer
	 * Sort. Iterates through nested arrays.
	 */
	private Sort translateArraySort(final Sort sort) {
		return IntBlastingWrapper.translateSort(mMgdScript.getScript(), sort);
	}

	/*
	 * translate variables and uninterpreted constants of bit-vector sort or
	 * array sort adds bv and int variable to mVariableMap and mReversedVarMap
	 * returns the new variable (translation results)
	 */
	private Term translateVars(final Term term, final boolean addToVarMap) {
		final boolean declareFun = true;
		if (declareFun) {
			String name;
			final Term intVar;
			if (term instanceof TermVariable) {
				name = ((TermVariable) term).getName();
				if (SmtSortUtils.isBitvecSort(term.getSort())) {
					intVar = mScript.variable(name, SmtSortUtils.getIntSort(mMgdScript));
				} else {
					intVar = mScript.variable(name, IntBlastingWrapper.translateSort(mScript, term.getSort()));
				}

			} else if (term instanceof ApplicationTerm) {
				name = ((ApplicationTerm) term).getFunction().getName();
				if (((ApplicationTerm) term).getParameters().length > 0) {
					throw new AssertionError("We support only constant symbols, not general function symbols");
				}
				intVar = mScript.term(name);
			} else {
				throw new AssertionError("Unsupported term");
			}

			mVariableMap.put(term, intVar);
			mReversedVarMap.put(intVar, term);
			return intVar;
		}

		if (mVariableMap.containsKey(term)) {
			mReversedVarMap.put(mVariableMap.get(term), term);
			return mVariableMap.get(term);
		} else {
			final Sort sort = term.getSort();
			if (SmtSortUtils.isArraySort(sort)) {
				Term arrayVar;
				arrayVar = mMgdScript.constructFreshTermVariable("arrayVar", translateArraySort(sort));
				if (!(term instanceof TermVariable)) {
					arrayVar = SmtUtils.termVariable2constant(mScript, (TermVariable) arrayVar, true);
				}
				if (addToVarMap) {
					mVariableMap.put(term, arrayVar);
					mReversedVarMap.put(arrayVar, term);
				}
				return arrayVar;
			} else if (SmtSortUtils.isBitvecSort(sort)) {
				Term intVar;
				intVar = mMgdScript.constructFreshTermVariable("intVar", SmtSortUtils.getIntSort(mScript));
				if (!(term instanceof TermVariable)) {
					intVar = SmtUtils.termVariable2constant(mScript, (TermVariable) intVar, true);
				}
				if (addToVarMap) {
					mVariableMap.put(term, intVar);
					mReversedVarMap.put(intVar, term);
				}
				return intVar;
			} else {
				return term;
			}

		}

	}

	/*
	 * translates quantified formulas, adds constraints for translated
	 * quantified variables in their scope
	 */
	@Override
	public void postConvertQuantifier(final QuantifiedFormula old, final Term newBody) {
		final HashSet<TermVariable> newTermVars = new HashSet<TermVariable>();
		final HashSet<Term> tvConstraints = new HashSet<Term>();
		if (newBody != old.getSubformula()) {
			for (int i = 0; i < old.getVariables().length; i++) {
				if (SmtSortUtils.isBitvecSort(old.getVariables()[i].getSort())) {

					final TermVariable freshQVar =
							mScript.variable(old.getVariables()[i].getName(), SmtSortUtils.getIntSort(mMgdScript));
					newTermVars.add(freshQVar);
					if (!mNutzTransformation) {
						tvConstraints.add(mTc.getTvConstraint(old.getVariables()[i], freshQVar));
					}

				} else if (SmtSortUtils.isArraySort(old.getVariables()[i].getSort())) {
					final Term newQuantifiedVar = mVariableMap.get(old.getVariables()[i]);
					assert mVariableMap.get(old.getVariables()[i]) != null;
					newTermVars.add((TermVariable) newQuantifiedVar);

					final Term arrayConstraint = mArrayConstraintMap.get(newQuantifiedVar);
					if (arrayConstraint != null) {
						tvConstraints.add(arrayConstraint);
					}

					mArrayConstraintMap.remove(newQuantifiedVar);
				} else {
					final TermVariable freshQVar = mScript.variable(old.getVariables()[i].getName(),
							IntBlastingWrapper.translateSort(mScript, old.getVariables()[i].getSort()));
					newTermVars.add(freshQVar);
				}
			}

			setResult(SmtUtils.quantifier(mScript, old.getQuantifier(), newTermVars,
					QuantifierUtils.applyDualFiniteConnective(mScript, old.getQuantifier(), newBody, QuantifierUtils
							.negateIfUniversal(mScript, old.getQuantifier(), SmtUtils.and(mScript, tvConstraints)))));
			return;
		} else {
			super.postConvertQuantifier(old, newBody);
		}
	}

	private boolean overaproxWithVars(final ApplicationTerm appTerm) {
		final FunctionSymbol fsym = appTerm.getFunction();
		if (fsym.isIntern()) {
			switch (fsym.getName()) {
			case "bvand":
			case "bvor":
			case "bvxor":
			case "bvashr":
			case "bvshl":
			case "bvlshr": {
				return true;
			}
			default: {
				// not a bit-wise function symbol
				return false;
			}
			}
		}
		return false;
	}

	/*
	 * TODO more modular
	 */
	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] args) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		final BigInteger two = BigInteger.valueOf(2);
		final FunctionSymbol fsym = appTerm.getFunction();

		if (fsym.isIntern()) {
			switch (fsym.getName()) {
			case "and": {
				setResult(SmtUtils.and(mNewScript, args));
				return;
			}
			case "or": {
				setResult(SmtUtils.or(mNewScript, args));
				return;
			}
			case "not": {
				setResult(SmtUtils.not(mNewScript, args[0]));
				return;
			}
			case "=>": {
				assert args.length == 2;
				setResult(SmtUtils.implies(mNewScript, args[0], args[1]));
				return;
			}
			case "store": {
				assert args.length == 3;

				if (mNutzTransformation && SmtSortUtils.isBitvecSort(appTerm.getParameters()[1].getSort())) {
					final int width = Integer.valueOf(appTerm.getParameters()[1].getSort().getIndices()[0]);
					// maximal representable number by a bit-vector of width
					// "width" plus one
					final Term maxNumberPlusOne =
							SmtUtils.rational2Term(mScript, Rational.valueOf(two.pow(width), BigInteger.ONE), intSort);
					final Term mod = SmtUtils.mod(mScript, args[1], maxNumberPlusOne);
					setResult(SmtUtils.store(mNewScript, args[0], mod, args[2]));
					return;
				} else {
					setResult(SmtUtils.store(mNewScript, args[0], args[1], args[2]));
					return;
				}
			}
			case "select": {
				assert args.length == 2;
				if (SmtSortUtils.isBitvecSort(appTerm.getSort())) {
					Term index;
					if (!mNutzTransformation) {
						// select terms can act as variables

						mArrayConstraintMap.put(args[0],
								mTc.getSelectConstraint(appTerm, mScript.term(fsym.getName(), args)));
						index = args[1];
					} else {
						final int width = Integer.valueOf(appTerm.getParameters()[1].getSort().getIndices()[0]);
						// maximal representable number by a bit-vector of width
						// "width" plus one
						final Term maxNumberPlusOne = SmtUtils.rational2Term(mScript,
								Rational.valueOf(two.pow(width), BigInteger.ONE), intSort);
						final Term mod = SmtUtils.mod(mScript, args[1], maxNumberPlusOne);
						index = mod;
					}

					setResult(SmtUtils.select(mNewScript, args[0], index));
					return;
				} else {
					setResult(SmtUtils.select(mNewScript, args[0], args[1]));
					return;
				}

			}
			}
		}

		if (appTerm.getParameters().length == 0) {
			if (fsym.getName().matches(BITVEC_CONST_PATTERN)) {
				final BigInteger constValue = new BigInteger(fsym.getName().substring(2));
				final Term intConst =
						SmtUtils.rational2Term(mScript, Rational.valueOf(constValue, BigInteger.ONE), intSort);

				setResult(intConst);
				return;
			} else if (SmtUtils.isFalseLiteral(appTerm)) {
				setResult(mScript.term("false"));
				return;
			} else if (SmtUtils.isTrueLiteral(appTerm)) {
				setResult(mScript.term("true"));
				return;
			} else {
				setResult(mVariableMap.get(appTerm));
				return;
			}
		} else if (appTerm.getParameters().length == 1
				&& SmtSortUtils.isBitvecSort(appTerm.getParameters()[0].getSort())) {
			// width of the first argument
			final int width = Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]);
			// maximal representable number by a bit-vector of width "width"
			// plus one
			final Term maxNumberPlusOne =
					SmtUtils.rational2Term(mScript, Rational.valueOf(two.pow(width), BigInteger.ONE), intSort);

			final Term translatedLHS = args[0];
			if (fsym.isIntern()) {
				switch (fsym.getName()) {
				case "bvnot": {
					final Term not = SmtUtils.unfTerm(mScript, "-", null, SmtSortUtils.getIntSort(mMgdScript),
							maxNumberPlusOne, SmtUtils.unfTerm(mScript, "+", null, SmtSortUtils.getIntSort(mMgdScript),
									translatedLHS, SmtUtils.rational2Term(mScript, Rational.ONE, intSort)));

					setResult(not);
					return;
				}
				case "bvneg": {
					final Term negation = SmtUtils.unfTerm(mScript, "-", null, SmtSortUtils.getIntSort(mMgdScript),
							maxNumberPlusOne, translatedLHS);
					if (mNutzTransformation) {
						arithmeticBvCount += 1;
						setResult(negation);
						return;
					}
					moduloCount += 1;
					arithmeticBvCount += 1;
					setResult(SmtUtils.mod(mScript, negation, maxNumberPlusOne));
					return;
				}
				case "extract": {
					setResult(translateExtract(appTerm, translatedLHS));
					return;
				}
				case "zero_extend":
					concatCount += 1;
					if (mNutzTransformation) {
						final Term maxNumber = SmtUtils.rational2Term(mScript,
								Rational.valueOf(two.pow(width), BigInteger.ONE), intSort);
						moduloCount += 1;
						setResult(SmtUtils.mod(mScript, args[0], maxNumber));
						return;
					}
					setResult(args[0]);
					return;
				case "const":
					setResult(mScript.term("const", null, translateArraySort(appTerm.getSort()), args));
					return;
				case "repeat":
				case "rotate_left":
				case "rotate_right":
				default:
					throw new UnsupportedOperationException("unexpected function: " + fsym.getName());
				}
			}
		} else {
			int width = 0;
			if (SmtSortUtils.isBitvecSort(appTerm.getParameters()[0].getSort())) {
				width = Integer.valueOf(appTerm.getParameters()[1].getSort().getIndices()[0]);
			}
			final Term maxNumber =
					SmtUtils.rational2Term(mScript, Rational.valueOf(two.pow(width), BigInteger.ONE), intSort);
			final Term[] translatedArgs = args;
			if (fsym.isIntern()) {
				switch (fsym.getName()) {
				case "=":
				case "distinct":
				case "bvult":
				case "bvule":
				case "bvugt":
				case "bvuge":
				case "bvslt":
				case "bvsle":
				case "bvsgt":
				case "bvsge": {
					setResult(translateRelations(appTerm, fsym, args, maxNumber, width));
					return;
				}
				case "bvadd": {
					final Term addition =
							SmtUtils.unfTerm(mScript, "+", null, SmtSortUtils.getIntSort(mMgdScript), translatedArgs);
					arithmeticBvCount += 1;
					if (mNutzTransformation) {
						setResult(addition);
						return;
					}
					moduloCount += 1;
					setResult(SmtUtils.mod(mScript, addition, maxNumber));
					return;
				}
				case "bvsub": {
					arithmeticBvCount += 1;
					final Term substraction =
							SmtUtils.unfTerm(mScript, "-", null, SmtSortUtils.getIntSort(mMgdScript), translatedArgs);
					if (mNutzTransformation) {
						setResult(substraction);
						return;
					}
					moduloCount += 1;
					setResult(SmtUtils.mod(mScript, substraction, maxNumber));
					return;
				}
				case "bvmul": {
					arithmeticBvCount += 1;
					final Term multiplication =
							SmtUtils.unfTerm(mScript, "*", null, SmtSortUtils.getIntSort(mMgdScript), translatedArgs);
					if (mNutzTransformation) {
						setResult(multiplication);
						return;
					}
					moduloCount += 1;
					setResult(SmtUtils.mod(mScript, multiplication, maxNumber));
					return;
				}
				case "ite": {
					setResult(SmtUtils.ite(mScript, args[0], args[1], args[2]));
					return;
				}
				}

				if (appTerm.getParameters().length == 2) {
					final Term translatedLHS = translatedArgs[0];
					final Term translatedRHS = translatedArgs[1];
					switch (fsym.getName()) {
					case "bvshl": {
						shiftsCount += 1;
						setResult(translateBvshl(translatedLHS, translatedRHS, width, maxNumber));
						return;
					}
					case "bvlshr": {
						shiftsCount += 1;
						setResult(translateBvlshr(translatedLHS, translatedRHS, width, maxNumber));
						return;
					}

					case "bvashr": {
						shiftsCount += 1;
						throw new UnsupportedOperationException(fsym.getName());
					}
					case "concat": {
						concatCount += 1;
						final Term multiplication = SmtUtils.unfTerm(mScript, "*", null,
								SmtSortUtils.getIntSort(mMgdScript), translatedLHS, maxNumber);
						if (mNutzTransformation) {
							moduloCount += 1;
							setResult(SmtUtils.unfTerm(mScript, "+", null, SmtSortUtils.getIntSort(mMgdScript),
									multiplication, SmtUtils.mod(mScript, translatedRHS, maxNumber)));
							return;
						}
						setResult(SmtUtils.unfTerm(mScript, "+", null, SmtSortUtils.getIntSort(mMgdScript),
								multiplication, translatedRHS));
						return;
					}

					case "bvudiv": {
						arithmeticBvCount += 1;
						bvdivBvmodCount += 1;
						setResult(translateBvudiv(translatedLHS, translatedRHS, maxNumber));
						return;
					}

					case "bvurem": {
						arithmeticBvCount += 1;
						bvdivBvmodCount += 1;
						setResult(translateBvurem(translatedLHS, translatedRHS, maxNumber));
						return;
					}
					case "bvand": {
						bvandCount += 1;
						final boolean replaceUfIntand = true;
						if (replaceUfIntand) {
							setResult(mTc.bvandSUMforReplacement(width, translatedLHS, translatedRHS));
							return;
						} else {
							final Term intAnd =
									mScript.term(mTc.getIntAndFunctionSymbol().getName(), translatedLHS, translatedRHS);
							final boolean constraintsOverapproximate = mTc.bvandConstraint(intAnd, width);
							if (constraintsOverapproximate) {
								mIsOverapproximation = true;
							}
							setResult(intAnd);
							return;
						}

					}
					case "bvnand":
					case "bvcomp":
					case "bvsmod":
					default:
						throw new UnsupportedOperationException("unexpected function: " + fsym.getName());

					}
				} else {
					if (fsym.getName().equals("bvand") || fsym.getName().equals("bvnand")) {
						throw new UnsupportedOperationException(
								"Bitvector-to-integer translation does not support bvand with more than 2 parameters.");
					}
				}
			}

		}
		// TODO: This is the intended translation for uninterpreted function
		// symbols
		// currently it is applied to all functions that are not handled above.
		final Term result = mNewScript.term(appTerm.getFunction().getName(), args);
		setResult(result);
	}

	@Override
	public void postConvertLet(final LetTerm oldLet, final Term[] newValues, final Term newBody) {
		throw new UnsupportedOperationException("Let terms are not yet supported.");
	}

	private Term translateExtract(final ApplicationTerm appTerm, final Term translatedLHS) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		final BigInteger two = BigInteger.valueOf(2);
		final int lowerIndex = Integer.parseInt(appTerm.getFunction().getIndices()[1]);
		final int upperIndex = Integer.parseInt(appTerm.getFunction().getIndices()[0]);

		final Term divby =
				SmtUtils.rational2Term(mScript, Rational.valueOf(two.pow(lowerIndex), BigInteger.ONE), intSort);
		final Term modby = SmtUtils.rational2Term(mScript,
				Rational.valueOf(two.pow(upperIndex - lowerIndex + 1), BigInteger.ONE), intSort);
		moduloCount += 1;
		return SmtUtils.mod(mScript,
				SmtUtils.unfTerm(mScript, "div", null, SmtSortUtils.getIntSort(mMgdScript), translatedLHS, divby),
				modby);
	}

	private Term translateBvudiv(final Term translatedLHS, final Term translatedRHS, final Term maxNumber) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		Term rhs;
		Term lhs;
		if (mNutzTransformation) {
			moduloCount += 2;
			rhs = SmtUtils.mod(mScript, translatedRHS, maxNumber);
			lhs = SmtUtils.mod(mScript, translatedLHS, maxNumber);
		} else {
			rhs = translatedRHS;
			lhs = translatedLHS;
		}
		final Term ifTerm = SmtUtils.unfTerm(mScript, "=", null, SmtSortUtils.getIntSort(mMgdScript), rhs,
				SmtUtils.rational2Term(mScript, Rational.ZERO, intSort));
		final Term thenTerm = SmtUtils.unfTerm(mScript, "-", null, SmtSortUtils.getIntSort(mMgdScript), maxNumber,
				SmtUtils.rational2Term(mScript, Rational.ONE, intSort));
		final Term elseTerm = SmtUtils.unfTerm(mScript, "div", null, SmtSortUtils.getIntSort(mMgdScript), lhs, rhs);
		return SmtUtils.ite(mScript, ifTerm, thenTerm, elseTerm);
	}

	private Term translateBvurem(final Term translatedLHS, final Term translatedRHS, final Term maxNumber) {
		Term rhs;
		Term lhs;
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		if (mNutzTransformation) {
			moduloCount += 2;
			rhs = SmtUtils.mod(mScript, translatedRHS, maxNumber);
			lhs = SmtUtils.mod(mScript, translatedLHS, maxNumber);
		} else {
			rhs = translatedRHS;
			lhs = translatedLHS;
		}
		final Term ifTerm = SmtUtils.unfTerm(mScript, "=", null, SmtSortUtils.getIntSort(mMgdScript), rhs,
				SmtUtils.rational2Term(mScript, Rational.ZERO, intSort));
		final Term thenTerm = translatedLHS;
		final Term elseTerm = SmtUtils.mod(mScript, lhs, rhs);
		moduloCount += 1;
		return SmtUtils.ite(mScript, ifTerm, thenTerm, elseTerm);
	}

	private Term translateBvshl(Term translatedLHS, Term translatedRHS, final int width, final Term maxNumber) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);

		if (mNutzTransformation) {
			moduloCount += 2;
			translatedRHS = SmtUtils.mod(mScript, translatedRHS, maxNumber);
			translatedLHS = SmtUtils.mod(mScript, translatedLHS, maxNumber);
		}
		if (translatedRHS instanceof ConstantTerm) {
			final Term shift = SmtUtils.unfTerm(mScript, "*", null, SmtSortUtils.getIntSort(mMgdScript), translatedLHS,
					pow2(translatedRHS));
			moduloCount += 1;
			return SmtUtils.mod(mScript, shift, maxNumber);
		} else {
			Term iteChain = SmtUtils.rational2Term(mScript, Rational.ZERO, intSort);
			for (int i = width - 1; i >= 0; i--) {
				if (i == 0) {
					final Term constInt = SmtUtils.rational2Term(mScript, Rational.valueOf(0, 1), intSort);
					iteChain = SmtUtils.ite(mScript, SmtUtils.binaryEquality(mScript, constInt, translatedRHS),
							translatedLHS, iteChain);
				} else {
					final Rational powResult = Rational.valueOf(i, 1);
					final Term ifTerm = SmtUtils.unfTerm(mScript, "=", null, SmtSortUtils.getIntSort(mMgdScript),
							translatedRHS, SmtUtils.rational2Term(mScript, powResult, intSort));
					final BigInteger pow = BigInteger.valueOf(2).pow(i);
					final Term thenTerm;
					if (mNutzTransformation) {
						thenTerm = SmtUtils.unfTerm(mScript, "*", null, SmtSortUtils.getIntSort(mMgdScript),
								SmtUtils.rational2Term(mScript, Rational.valueOf(pow, BigInteger.ONE), intSort),
								translatedLHS);
					} else {
						moduloCount += 1;
						thenTerm =
								SmtUtils.mod(
										mScript, SmtUtils.unfTerm(mScript, "*", null,
												SmtSortUtils.getIntSort(mMgdScript), SmtUtils.rational2Term(mScript,
														Rational.valueOf(pow, BigInteger.ONE), intSort),
												translatedLHS),
										maxNumber);
					}
					iteChain = SmtUtils.ite(mScript, ifTerm, thenTerm, iteChain);
				}
			}
			moduloCount += 1;
			return iteChain;
		}
	}

	private Term translateBvlshr(Term translatedLHS, Term translatedRHS, final int width, final Term maxNumber) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);

		if (mNutzTransformation) {
			moduloCount += 1;
			translatedRHS = SmtUtils.mod(mScript, translatedRHS, maxNumber);
			translatedLHS = SmtUtils.mod(mScript, translatedLHS, maxNumber);
		}

		if (translatedRHS instanceof ConstantTerm) {
			final Term shift = SmtUtils.unfTerm(mScript, "div", null, SmtSortUtils.getIntSort(mMgdScript),
					translatedLHS, pow2(translatedRHS));
			return shift;
		} else {
			Term iteChain = SmtUtils.rational2Term(mScript, Rational.ZERO, intSort);
			for (int i = width - 1; i >= 0; i--) {
				if (i == 0) {
					final Term constInt = SmtUtils.rational2Term(mScript, Rational.valueOf(0, 1), intSort);
					iteChain = SmtUtils.ite(mScript, SmtUtils.unfTerm(mScript, "=", null,
							SmtSortUtils.getIntSort(mMgdScript), constInt, translatedRHS), translatedLHS, iteChain);
				} else {
					final Rational powResult = Rational.valueOf(i, 1);
					final Term ifTerm = SmtUtils.unfTerm(mScript, "=", null, SmtSortUtils.getIntSort(mMgdScript),
							translatedRHS, SmtUtils.rational2Term(mScript, powResult, intSort));
					final BigInteger pow = BigInteger.valueOf(2).pow(i);
					final Term thenTerm =
							SmtUtils.unfTerm(mScript, "div", null, SmtSortUtils.getIntSort(mMgdScript), translatedLHS,
									SmtUtils.rational2Term(mScript, Rational.valueOf(pow, BigInteger.ONE), intSort));
					iteChain = SmtUtils.ite(mScript, ifTerm, thenTerm, iteChain);
				}
			}
			moduloCount += 1;
			return iteChain;
		}
	}

	private Term translateRelations(final ApplicationTerm appTerm, final FunctionSymbol fsym, final Term[] args,
			final Term maxNumberPlusOne, final int width) {
		Term[] translatedArgs = new Term[args.length];
		final Term[] utsArgs = args;
		translatedArgs = args;

		if (mNutzTransformation && SmtSortUtils.isNumericSort(args[0].getSort())) {
			moduloCount += 2;
		}
		if (fsym.isIntern()) {
			switch (fsym.getName()) {
			case "=": {
				if (mNutzTransformation && SmtSortUtils.isNumericSort(args[0].getSort())) {
					for (int i = 0; i < args.length; i++) {
						translatedArgs[i] = SmtUtils.mod(mScript, args[i], maxNumberPlusOne);
					}
				}

				if (mNutzTransformation && SmtSortUtils.isArraySort(appTerm.getParameters()[0].getSort())) {
					if (SmtSortUtils.isBitvecSort(appTerm.getParameters()[0].getSort().getArguments()[1])) {
						final TermVariable quantifiedVar =
								mNewScript.variable("AuxVar", SmtSortUtils.getIntSort(mNewScript));

						final Term bounds = SmtUtils.and(mNewScript,
								SmtUtils.leq(mNewScript,
										SmtUtils.rational2Term(mNewScript, Rational.ZERO,
												SmtSortUtils.getIntSort(mNewScript)),
										quantifiedVar),
								SmtUtils.leq(mNewScript, quantifiedVar, maxNumberPlusOne));
						final Term equality =
								SmtUtils.equality(mNewScript, SmtUtils.select(mNewScript, args[0], quantifiedVar),
										SmtUtils.select(mNewScript, args[1], quantifiedVar));
						final Term subfromuls = SmtUtils.implies(mNewScript, bounds, equality);
						final HashSet<TermVariable> newTermVars = new HashSet<TermVariable>();
						newTermVars.add(quantifiedVar);
						final Term quantifiedEq = SmtUtils.quantifier(mNewScript, 1, newTermVars, subfromuls);
						final Term quantifiedEqImpliesEq =
								SmtUtils.implies(mNewScript, quantifiedEq, SmtUtils.equality(mNewScript, args));
						mArrayConstraintMap.put(appTerm, quantifiedEqImpliesEq);
					}
				}

				return SmtUtils.unfTerm(mScript, "=", null, SmtSortUtils.getIntSort(mMgdScript), translatedArgs);
			}
			case "distinct": {
				if (mNutzTransformation && SmtSortUtils.isNumericSort(args[0].getSort())) {
					for (int i = 0; i < args.length; i++) {
						translatedArgs[i] = SmtUtils.mod(mScript, args[i], maxNumberPlusOne);

					}
				}
				return SmtUtils.unfTerm(mScript, "distinct", null, SmtSortUtils.getIntSort(mMgdScript), translatedArgs);

			}
			case "bvult": {
				if (mNutzTransformation) {
					for (int i = 0; i < args.length; i++) {
						translatedArgs[i] = SmtUtils.mod(mScript, args[i], maxNumberPlusOne);

					}
				}
				return SmtUtils.less(mScript, translatedArgs[0], translatedArgs[1]);

			}
			case "bvule": {
				if (mNutzTransformation) {
					for (int i = 0; i < args.length; i++) {
						translatedArgs[i] = SmtUtils.mod(mScript, args[i], maxNumberPlusOne);
					}
				}
				return SmtUtils.leq(mScript, translatedArgs[0], translatedArgs[1]);

			}
			case "bvugt": {
				if (mNutzTransformation) {
					for (int i = 0; i < args.length; i++) {
						translatedArgs[i] = SmtUtils.mod(mScript, args[i], maxNumberPlusOne);
					}
				}
				return SmtUtils.greater(mScript, translatedArgs[0], translatedArgs[1]);

			}
			case "bvuge": {
				if (mNutzTransformation) {
					for (int i = 0; i < args.length; i++) {
						translatedArgs[i] = SmtUtils.mod(mScript, args[i], maxNumberPlusOne);
					}
				}
				return SmtUtils.geq(mScript, translatedArgs[0], translatedArgs[1]);

			}
			case "bvslt": {
				for (int i = 0; i < args.length; i++) {
					utsArgs[i] = uts(width, args[i], mNutzTransformation);
				}

				return SmtUtils.less(mScript, utsArgs[0], utsArgs[1]);
			}
			case "bvsle": {
				for (int i = 0; i < args.length; i++) {
					utsArgs[i] = uts(width, args[i], mNutzTransformation);
				}
				return SmtUtils.leq(mScript, utsArgs[0], utsArgs[1]);

			}
			case "bvsgt": {
				for (int i = 0; i < args.length; i++) {
					utsArgs[i] = uts(width, args[i], mNutzTransformation);
				}
				return SmtUtils.greater(mScript, utsArgs[0], utsArgs[1]);
			}
			case "bvsge": {
				for (int i = 0; i < args.length; i++) {
					utsArgs[i] = uts(width, args[i], mNutzTransformation);
				}
				return SmtUtils.geq(mScript, utsArgs[0], utsArgs[1]);

			}
			}
		}
		throw new UnsupportedOperationException("unexpected relation");
	}

	// unsigned to signed for relations
	private final Term uts(final int width, final Term term, final boolean nutz) {
		// 2 * (x mod 2^(k - 1) ) - x
		utsCount += 1;
		final Sort intSort = SmtSortUtils.getIntSort(mScript);

		final Term two =
				SmtUtils.rational2Term(mScript, Rational.valueOf(BigInteger.valueOf(2), BigInteger.ONE), intSort);
		final Term twoPowWidth = SmtUtils.rational2Term(mScript,
				Rational.valueOf(BigInteger.valueOf(2).pow(width - 1), BigInteger.ONE), intSort);

		if (nutz) {
			final Term nutzPow = SmtUtils.rational2Term(mScript,
					Rational.valueOf(BigInteger.valueOf(2).pow(width), BigInteger.ONE), intSort);
			final Term modulo = SmtUtils.mod(mScript, SmtUtils.mod(mScript, term, nutzPow), twoPowWidth);

			return SmtUtils.unfTerm(mScript, "-", null, SmtSortUtils.getIntSort(mMgdScript),
					SmtUtils.unfTerm(mScript, "*", null, SmtSortUtils.getIntSort(mMgdScript), two, modulo),
					SmtUtils.mod(mScript, term, nutzPow));
		} else {
			final Term modulo = SmtUtils.mod(mScript, term, twoPowWidth);
			return SmtUtils.unfTerm(mScript, "-", null, SmtSortUtils.getIntSort(mMgdScript),
					SmtUtils.unfTerm(mScript, "*", null, SmtSortUtils.getIntSort(mMgdScript), two, modulo), term);
		}

	}

	// calculates power of two if exponent is a constant, otherwise this is not
	// implemented in the SMT integer theory
	private Term pow2(final Term term) {
		assert term.getSort().isNumericSort();
		if (term instanceof ConstantTerm) {
			final Sort intSort = SmtSortUtils.getIntSort(mScript);
			final ConstantTerm constTerm = (ConstantTerm) term;
			final Term twoPow;
			if (constTerm.getValue() instanceof Rational) {
				final Rational ratint = (Rational) constTerm.getValue();
				twoPow = SmtUtils.rational2Term(mScript,
						Rational.valueOf(BigInteger.valueOf(2).pow(ratint.numerator().intValueExact()), BigInteger.ONE),
						intSort);
			} else {
				final BigInteger bigint = (BigInteger) constTerm.getValue();
				twoPow = SmtUtils.rational2Term(mScript,
						Rational.valueOf(BigInteger.valueOf(2).pow(bigint.intValueExact()), BigInteger.ONE), intSort);
			}
			return twoPow;
		}
		throw new UnsupportedOperationException("function pow2 not implemented");
		// return term;
	}

	private boolean isBitVecSort(final Sort sort) {
		if (sort.getName().equals("BitVec")) {
			return true;
		}
		return false;
	}

	public LinkedHashMap<Term, Term> getVarMap() {
		return mVariableMap;
	}

	public LinkedHashMap<Term, Term> getReversedVarMap() {
		return mReversedVarMap;
	}

	public Set<Term> getOverapproxVariables() {
		return mOverapproxVariables;
	}

	public boolean wasOverapproximation() {
		return mIsOverapproximation;
	}
}
