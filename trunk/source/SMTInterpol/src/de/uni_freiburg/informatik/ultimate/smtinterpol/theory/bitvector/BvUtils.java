/*
 * Copyright (C) 2020-2021 Max Barth (Max.Barth95@gmx.de)
 * Copyright (C) 2020-2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.LogicSimplifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IProofTracker;

public class BvUtils {
	private final Theory mTheory;
	private final LogicSimplifier mUtils;

	public BvUtils(final Theory theory, final LogicSimplifier utils) {
		mTheory = theory;
		mUtils = utils;
	}

	/**
	 * Returns True, if all arguments are ConstantTerm's Setting the return value of
	 * this function to false, will deactivate all BV constant optimizations
	 */
	public boolean isConstRelation(final Term lhs, final Term rhs) {
		return isConstant(lhs) && isConstant(rhs);
	}

	public boolean isConstant(final Term term) {
		return term instanceof ConstantTerm;
	}

	/**
	 * returns the bit string of #b or #x Constant Terms. (_bvi j) Constants are
	 * replaced by #b constants beforehand
	 */
	public BigInteger parseBitvectorConstant(final Term term) {
		if (!(term instanceof ConstantTerm)) {
			throw new UnsupportedOperationException("Can't convert to bitstring: " + term);
		}
		final ConstantTerm ct = (ConstantTerm) term;
		assert ct.getSort().isBitVecSort();
		if (ct.getValue() instanceof String) {
			String bitString = (String) ct.getValue();
			if (bitString.startsWith("#b")) {
				bitString = (String) ct.getValue();
				return new BigInteger(bitString.substring(2), 2);
			} else if (bitString.startsWith("#x")) {
				// #xX of sort (_ BitVec m) where m is 4 times the number of digits in X.
				return new BigInteger(bitString.substring(2), 16);
			} else {
				throw new AssertionError("Unexpected bitvector constant: " + bitString);
			}
		} else {
			return (BigInteger) ct.getValue();
		}
	}

	/**
	 * replaces (_bvi j) constants by #b constants
	 */
	public Term getBvConstAsBinaryConst(final FunctionSymbol fsym, final Sort sort) {
		if (sort.isBitVecSort()) {
			final String name = fsym.getName();
			assert name.matches("bv\\d+");
			String value = new BigInteger(name.substring(2)).toString(2);
			final int size = Integer.valueOf(sort.getIndices()[0]);
			if (value.length() > size) {
				final int overhead = value.length() - size;
				value = value.substring(overhead);
			} else {
				final String repeated = new String(new char[size - value.length()]).replace("\0", "0");
				value = repeated + value;
			}
			final Term bitString = mTheory.binary("#b" + value);
			assert bitString.getSort().equals(sort);
			return mTheory.binary("#b" + value);
		}
		throw new UnsupportedOperationException("Can't convert bv constant: " + fsym.getName());
	}

	/*
	 * normalization of bitvec equalities, eliminates concatenations with perfect
	 * match: a :: b = c :: d replaced by a = c && c = d with a,c and b, d being of
	 * same size.
	 */
	private Term eliminateConcatPerfectMatch(final FunctionSymbol fsym, final Term lhs, final Term rhs) {
		assert fsym.getName().equals("=");
		final List<Term> matchresult = new ArrayList<>();

		if (!((lhs instanceof ApplicationTerm) && (rhs instanceof ApplicationTerm))) {
			return null;
		}
		final ApplicationTerm aplhs = (ApplicationTerm) lhs;
		final ApplicationTerm aprhs = (ApplicationTerm) rhs;
		if (!(aplhs.getFunction().getName().equals("concat") && aprhs.getFunction().getName().equals("concat"))) {
			return null;
		}
		if (aplhs.getParameters()[0].getSort().getIndices().equals(aprhs.getParameters()[0].getSort().getIndices())) {
			final Term matchConj1 = mTheory.term("=", aplhs.getParameters()[0], aprhs.getParameters()[0]);
			final Term matchConj2 = mTheory.term("=", aplhs.getParameters()[1], aprhs.getParameters()[1]);
			matchresult.add(simplifyBinaryBitVecEquality(matchConj1));
			matchresult.add(simplifyBinaryBitVecEquality(matchConj2));
		} else {
			return null;
		}

		Term[] result = new Term[matchresult.size()];
		result = matchresult.toArray(result);
		return mTheory.and(result);
	}

	/*
	 * eliminates concatenations with NO match: That means, a,b and c have different
	 * size; a :: b = c is replaced by b = extract(0, b.length, c) AND a = extract(
	 * b.length , a.length, c) Can only be called on binary equalities.
	 */
	private Term eliminateConcatNoMatch(final FunctionSymbol fsym, final Term lhs, final Term rhs) {
		assert fsym.getName().equals("=");
		assert lhs.getSort().isBitVecSort();
		assert rhs.getSort().isBitVecSort();

		ApplicationTerm apTermConcat = null;
		Term concatResult = null;
		if (lhs instanceof ApplicationTerm) {
			if (((ApplicationTerm) lhs).getFunction().getName().equals("concat")) {
				apTermConcat = (ApplicationTerm) lhs;
				concatResult = rhs;
			}
		}
		if (rhs instanceof ApplicationTerm) {
			if (((ApplicationTerm) rhs).getFunction().getName().equals("concat")) {
				if (concatResult != null) {
					// concat on both sides
					// select propagation will take care of this
				} else {
					apTermConcat = (ApplicationTerm) rhs;
					concatResult = lhs;
				}

			}
		}
		if ((apTermConcat == null) || (concatResult == null)) {
			return null;
		}

		// selectIndices[0] >= selectIndices[1]
		final String[] selectIndices1 = new String[2];
		selectIndices1[0] = String
				.valueOf((Integer.parseInt(apTermConcat.getParameters()[1].getSort().getIndices()[0]) - 1));
		selectIndices1[1] = "0";
		// (_ extract i j)
		final FunctionSymbol extractLower = mTheory.getFunctionWithResult("extract", selectIndices1, null,
				concatResult.getSort());
		final Term extractLowerConcatResult = propagateExtract(extractLower, concatResult);
		final String[] selectIndices2 = new String[2];
		selectIndices2[0] = String.valueOf((Integer.parseInt(concatResult.getSort().getIndices()[0]) - 1));
		selectIndices2[1] = String.valueOf((Integer.parseInt(concatResult.getSort().getIndices()[0])
				- Integer.parseInt(apTermConcat.getParameters()[0].getSort().getIndices()[0])));
		final FunctionSymbol extractHigher = mTheory.getFunctionWithResult("extract", selectIndices2, null,
				concatResult.getSort());

		final Term extractHigherConcatResult = propagateExtract(extractHigher, concatResult);

		final Term matchConj1 = mTheory.term("=", apTermConcat.getParameters()[0], extractHigherConcatResult);
		final Term matchConj2 = mTheory.term("=", apTermConcat.getParameters()[1], extractLowerConcatResult);

		return mTheory.and(simplifyBinaryBitVecEquality(matchConj1), simplifyBinaryBitVecEquality(matchConj2));
	}

	/*
	 * bvadd, bvudiv, bvmul
	 */
	public Term simplifyBitvectorConstantOp(final FunctionSymbol fsym, final Term lhs, final Term rhs) {
		final BigInteger lhsInt = parseBitvectorConstant(lhs);
		final BigInteger rhsInt = parseBitvectorConstant(rhs);
		BigInteger result;
		final int size = Integer.valueOf(lhs.getSort().getIndices()[0]);
		final BigInteger mask = BigInteger.ONE.shiftLeft(size).subtract(BigInteger.ONE);
		assert fsym.isIntern();
		switch (fsym.getName()) {
		case SMTLIBConstants.BVADD: {
			result = lhsInt.add(rhsInt).and(mask);
			break;
		}
		case SMTLIBConstants.BVUDIV: {
			// truncated integer division
			result = rhsInt.signum() == 0 ? mask : lhsInt.divide(rhsInt);
			break;
		}
		case SMTLIBConstants.BVUREM: {
			result = rhsInt.signum() == 0 ? lhsInt : lhsInt.mod(rhsInt);
			break;
		}
		case SMTLIBConstants.BVMUL: {
			// multiplication mod 2^m
			result = lhsInt.multiply(rhsInt).and(mask);
			break;
		}
		case SMTLIBConstants.BVSUB: {
			result = lhsInt.subtract(rhsInt).and(mask);
			break;
		}
		case SMTLIBConstants.BVAND: {
			result = lhsInt.and(rhsInt);
			break;
		}
		case SMTLIBConstants.BVOR: {
			result = lhsInt.or(rhsInt);
			break;
		}
		case SMTLIBConstants.BVXOR: {
			result = lhsInt.xor(rhsInt);
			break;
		}
		case SMTLIBConstants.BVNAND: {
			result = lhsInt.and(rhsInt).xor(mask);
			break;
		}
		case SMTLIBConstants.BVNOR: {
			result = lhsInt.or(rhsInt).xor(mask);
			break;
		}
		case SMTLIBConstants.BVXNOR: {
			result = lhsInt.xor(rhsInt).xor(mask);
			break;
		}
		default:
			throw new UnsupportedOperationException("unknown function symbol: " + fsym.getName());
		}
		return mTheory.constant(result, fsym.getReturnSort());
	}

	public Term simplifyConcatConst(final FunctionSymbol fsym, final Term lhs, final Term rhs) {
		assert fsym.getName().equals("concat");
		final int rightSize = Integer.valueOf(rhs.getSort().getIndices()[0]);
		final BigInteger result = parseBitvectorConstant(lhs).shiftLeft(rightSize).or(parseBitvectorConstant(rhs));
		return mTheory.constant(result, fsym.getReturnSort());
	}

	/*
	 * bvshl, bvlshr
	 */
	public Term simplifyShiftConst(final FunctionSymbol fsym, final Term lhs, final Term rhs) {
		final BigInteger lhsBigInt = parseBitvectorConstant(lhs);
		final BigInteger rhsBigInt = parseBitvectorConstant(rhs);
		final int lhsSize = Integer.parseInt(lhs.getSort().getIndices()[0]);
		final BigInteger result;
		if (fsym.getName().equals("bvshl")) {
			if (BigInteger.valueOf(lhsSize).compareTo(rhsBigInt) <= 0) {
				result = BigInteger.ZERO;
			} else {
				final BigInteger mask = BigInteger.ONE.shiftLeft(lhsSize).subtract(BigInteger.ONE);
				result = lhsBigInt.shiftLeft(rhsBigInt.intValueExact()).and(mask);
			}
		} else if (fsym.getName().equals("bvlshr")) {
			if (BigInteger.valueOf(lhsSize).compareTo(rhsBigInt) <= 0) {
				result = BigInteger.ZERO;
			} else {
				result = lhsBigInt.shiftRight(rhsBigInt.intValueExact());
			}

		} else {
			throw new UnsupportedOperationException("unknown function symbol: " + fsym.getName());
		}

		return mTheory.constant(result, fsym.getReturnSort());
	}

	public Term simplifyNegConst(final FunctionSymbol fsym, final Term term) {
		assert fsym.getName().equals("bvneg");
		final int size = Integer.valueOf(term.getSort().getIndices()[0]);
		final BigInteger bigint = parseBitvectorConstant(term);
		if (bigint.equals(BigInteger.ZERO)) {
			return term;
		}
		final BigInteger result = BigInteger.ONE.shiftLeft(size).subtract(bigint);
		return mTheory.constant(result, fsym.getReturnSort());
	}

	public Term simplifyNotConst(final FunctionSymbol fsym, final Term term) {
		final int size = Integer.valueOf(term.getSort().getIndices()[0]);
		final BigInteger bigint = parseBitvectorConstant(term);
		final BigInteger result = BigInteger.ONE.shiftLeft(size).subtract(BigInteger.ONE).subtract(bigint);
		return mTheory.constant(result, fsym.getReturnSort());
	}

	public Term simplifySelectConst(final FunctionSymbol fsym, final Term term) {
		// (_ extract i j)
		// (_ BitVec l), 0 <= j <= i < l
		// (_ extract 7 5) 00100000 = 001
		// (_ extract 7 7) 10000000 = 1
		// Result length = i - j + 1
		assert fsym.getName().equals("extract");
		final BigInteger value = parseBitvectorConstant(term);
		final int high = Integer.parseInt(fsym.getIndices()[1]);
		final int low = Integer.parseInt(fsym.getIndices()[0]);
		final BigInteger mask = BigInteger.ONE.shiftLeft(high - low + 1).subtract(BigInteger.ONE);
		final BigInteger result = value.shiftLeft(low).and(mask);
		return mTheory.constant(result, fsym.getReturnSort());
	}

	public Term simplifyBvultConst(final FunctionSymbol fsym, final Term lhs, final Term rhs) {
		if (fsym != null) {
			assert fsym.getName().equals("bvult");
		}
		final BigInteger lhsValue = parseBitvectorConstant(lhs);
		final BigInteger rhsValue = parseBitvectorConstant(rhs);
		return lhsValue.compareTo(rhsValue) <= 0 ? mTheory.mTrue : mTheory.mFalse;
	}

	public Term simplifyBvslXConst(final FunctionSymbol fsym, final Term lhs, final Term rhs) {
		assert fsym.getName().equals("bvslt") || fsym.getName().equals("bvsle");
		final BigInteger lhsValue = parseBitvectorConstant(lhs);
		final BigInteger rhsValue = parseBitvectorConstant(rhs);
		final int size = Integer.valueOf(lhs.getSort().getIndices()[0]);
		final BigInteger sign = BigInteger.ONE.shiftLeft(size - 1);

		final int comparison = lhsValue.xor(sign).compareTo(rhsValue.xor(sign));
		if (fsym.getName().equals("bvslt") ? comparison < 0 : comparison <= 0) {
			return mTheory.mTrue;
		} else {
			return mTheory.mFalse;
		}
	}

	/*
	 * TODO add proof for all const optimizations
	 */
	public Term getProof(final Term optimized, final Term convertedApp, final IProofTracker tracker,
			final Annotation proofconst) {
		final Term lhs = tracker.getProvedTerm(convertedApp);
		final Term rewrite = tracker.buildRewrite(lhs, optimized, proofconst);
		// return mTracker.transitivity(mConvertedApp, rewrite);
		return tracker.intern(convertedApp, rewrite); // wenn in einem literal
	}

	/**
	 * replaces every inequality by its bvult abbreviation. Applies a few
	 * simplifications on constant terms and simple equalities uses recursion in
	 * some cases
	 */
	public Term getBvultTerm(final Term convert) {
		final ApplicationTerm appterm;
		if (convert instanceof ApplicationTerm) {
			appterm = (ApplicationTerm) convert;
		} else if (convert instanceof AnnotatedTerm) {
			final AnnotatedTerm convAnno = (AnnotatedTerm) convert;
			appterm = (ApplicationTerm) convAnno.getSubterm();
		} else {
			throw new UnsupportedOperationException("Not an Inequality");
		}
		assert appterm.getParameters().length == 2;
		final int size = Integer.valueOf(appterm.getParameters()[0].getSort().getIndices()[0]);
		final FunctionSymbol fsym = appterm.getFunction();
		final Theory theory = convert.getTheory();
		// selectIndices[0] >= selectIndices[1]
		final String[] selectIndices = new String[2];
		final int signBitIndex = size - 1;
		selectIndices[0] = String.valueOf(signBitIndex);
		selectIndices[1] = String.valueOf(signBitIndex);
		// (_ extract i j)
		final FunctionSymbol extract = mTheory.getFunctionWithResult("extract", selectIndices, null,
				appterm.getParameters()[0].getSort());
		if (fsym.isIntern()) {
			switch (fsym.getName()) {
			case "bvult": {
				if (appterm.getParameters()[0].equals(appterm.getParameters()[1])) {
					return mTheory.mFalse;
				}
				if (isConstRelation(appterm.getParameters()[0], appterm.getParameters()[1])) {
					return simplifyBvultConst(appterm.getFunction(), appterm.getParameters()[0],
							appterm.getParameters()[1]);
				}
				return appterm;
			}
			case "bvslt": {
				if (appterm.getParameters()[0].equals(appterm.getParameters()[1])) {
					return mTheory.mFalse;
				}
				if (isConstRelation(appterm.getParameters()[0], appterm.getParameters()[1])) {
					return simplifyBvslXConst(appterm.getFunction(), appterm.getParameters()[0],
							appterm.getParameters()[1]);
				}
				final Term equiBvult = theory.or(
						theory.not(theory.or(
								theory.not(theory.term("=", theory.term(extract, appterm.getParameters()[0]),
										theory.binary("#b1"))),
								theory.not(theory.term("=", theory.term(extract, appterm.getParameters()[1]),
										theory.binary("#b0"))))),

						theory.not(theory.or(
								theory.not(theory.term("=", theory.term(extract, appterm.getParameters()[0]),
										theory.term(extract, appterm.getParameters()[1]))),
								theory.not(theory.term("bvult", appterm.getParameters()[0],
										appterm.getParameters()[1])))));
				return equiBvult;
			}
			case "bvule": {
				// (bvule s t) abbreviates (or (bvult s t) (= s t))
				final Term bvult = theory.term("bvult", appterm.getParameters()[0], appterm.getParameters()[1]);
				return theory.or(bvult, theory.term("=", appterm.getParameters()[0], appterm.getParameters()[1]));
			}
			case "bvsle": {
				if (isConstRelation(appterm.getParameters()[0], appterm.getParameters()[1])) {
					return simplifyBvslXConst(appterm.getFunction(), appterm.getParameters()[0],
							appterm.getParameters()[1]);
				}
				final Term bvult = theory.term("bvult", appterm.getParameters()[0], appterm.getParameters()[1]);
				final Term bvule = theory.or(bvult,
						theory.term("=", appterm.getParameters()[0], appterm.getParameters()[1]));
				final Term equiBvule = theory.or(
						theory.not(theory.or(
								theory.not(theory.term("=", theory.term(extract, appterm.getParameters()[0]),
										theory.binary("#b1"))),
								theory.not(theory.term("=", theory.term(extract, appterm.getParameters()[1]),
										theory.binary("#b0"))))),
						theory.not(
								theory.or(
										theory.not(theory.term("=", theory.term(extract, appterm.getParameters()[0]),
												theory.term(extract, appterm.getParameters()[1]))),
										theory.not(bvule))));

				return equiBvule;
			}
			case "bvugt": {
				if (appterm.getParameters()[0].equals(appterm.getParameters()[1])) {
					return mTheory.mFalse;
				}
				// (bvugt s t) abbreviates (bvult t s)
				if (isConstRelation(appterm.getParameters()[0], appterm.getParameters()[1])) {
					return simplifyBvultConst(null, appterm.getParameters()[1], appterm.getParameters()[0]);
				}
				return theory.term("bvult", appterm.getParameters()[1], appterm.getParameters()[0]);
			}
			case "bvsgt": {
				if (appterm.getParameters()[0].equals(appterm.getParameters()[1])) {
					return mTheory.mFalse;
				}
				// (bvsgt s t) abbreviates (bvslt t s)
				return getBvultTerm(theory.term("bvslt", appterm.getParameters()[1], appterm.getParameters()[0]));
			}
			case "bvuge": {
				// (bvuge s t) abbreviates (or (bvult t s) (= s t))
				final Term bvult;
				if (isConstRelation(appterm.getParameters()[0], appterm.getParameters()[1])) {
					bvult = simplifyBvultConst(null, appterm.getParameters()[1], appterm.getParameters()[0]);
				} else {
					bvult = theory.term("bvult", appterm.getParameters()[1], appterm.getParameters()[0]);
				}
				return theory.or(bvult, theory.term("=", appterm.getParameters()[0], appterm.getParameters()[1]));
			}
			case "bvsge": {
				// (bvsge s t) abbreviates (bvsle t s)
				return getBvultTerm(theory.term("bvsle", appterm.getParameters()[1], appterm.getParameters()[0]));
			}
			default: {
				throw new UnsupportedOperationException("Not an Inequality function symbol: " + fsym.getName());
			}
			}
		}
		throw new UnsupportedOperationException("Not an Inequality");
	}

	/**
	 * Bit Mask Elimination simplifies bvand, bvor functions where one hand side is
	 * a constant. We determine the result of the function as much as possible by
	 * the given constant (absorbingElement). everything else (neutralElement in the
	 * constant) is selected from the non-constant argument.
	 */
	public Term bitMaskElimination(final Term term) {
		Term bitMask = null;
		final String[] indices = new String[2];

		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appterm = (ApplicationTerm) term;
			final char absorbingElement;
			final char neutralElement;
			if (appterm.getFunction().getName().equals("bvand")) {
				absorbingElement = '0';
				neutralElement = '1';
			} else if (appterm.getFunction().getName().equals("bvor")) {
				absorbingElement = '1';
				neutralElement = '0';
			} else {
				return term;
			}
			final Term lhs = appterm.getParameters()[0];
			final Term rhs = appterm.getParameters()[1];
			final BigInteger constAsBigInt;
			Term varTerm;
			if (isConstant(lhs) && ((rhs instanceof TermVariable) || (rhs instanceof ApplicationTerm))) {
				constAsBigInt = parseBitvectorConstant(lhs);
				varTerm = rhs;
			} else if ((rhs instanceof ConstantTerm)
					&& ((lhs instanceof TermVariable) || (lhs instanceof ApplicationTerm))) {
				constAsBigInt = parseBitvectorConstant(rhs);
				varTerm = lhs;
			} else {
				return term;
			}

			final String constAsString = constAsBigInt.toString(2);

			String constSubString = "#b";
			indices[0] = String.valueOf(constAsString.length() - 1);

			for (int i = 0; i < constAsString.length(); i++) { // iterates from left to right over the BitVec
				final char ch = constAsString.charAt(i);
				if (ch == absorbingElement) {
					constSubString = constSubString + ch;
					if (i > 0) {
						if (constAsString.charAt(i - 1) == neutralElement) {
							// indices.clone() is important, otherwise the term changes by altering the
							// array!
							final FunctionSymbol extract = mTheory.getFunctionWithResult("extract", indices.clone(),
									null, appterm.getParameters()[0].getSort());
							final Term select = mTheory.term(extract, varTerm);

							if (bitMask != null) {
								bitMask = mTheory.term("concat", bitMask, select);
							} else {
								bitMask = select;
							}
						}
					}
					indices[0] = String.valueOf(constAsString.length() - i - 2);
					if (i == constAsString.length() - 1) {
						if (bitMask != null) {
							bitMask = mTheory.term("concat", bitMask, mTheory.binary(constSubString));
						} else {
							bitMask = mTheory.binary(constSubString);
						}
					}
				} else {
					if (!constSubString.equals("#b")) {
						if (bitMask != null) {
							bitMask = mTheory.term("concat", bitMask, mTheory.binary(constSubString));
						} else {
							bitMask = mTheory.binary(constSubString);
						}
					}
					constSubString = "#b";
					indices[1] = String.valueOf(constAsString.length() - i - 1);
					// Case end of Vector
					if (i == constAsString.length() - 1) {
						final FunctionSymbol extract = mTheory.getFunctionWithResult("extract", indices.clone(), null,
								appterm.getParameters()[0].getSort());
						final Term select = mTheory.term(extract, varTerm);
						if (bitMask != null) {
							bitMask = mTheory.term("concat", bitMask, select);
						} else {
							bitMask = select;
						}
					}
				}

			}
			return bitMask;
		}
		return term;
	}

	/**
	 * propagates a select over concat and bitwise functions to its arguments
	 * smallers the bitvec size of the function (less work for bitblasting)
	 */
	public Term propagateExtract(final FunctionSymbol fsym, final Term param) {
		assert fsym.getName().equals("extract");
		final int lowerIndex = Integer.parseInt(fsym.getIndices()[1]);
		final int upperIndex = Integer.parseInt(fsym.getIndices()[0]);
		assert lowerIndex <= upperIndex;
		if (param instanceof ApplicationTerm) {
			final ApplicationTerm subTerm = (ApplicationTerm) param;
			final FunctionSymbol subFsym = subTerm.getFunction();
			if (subFsym.isIntern()) {
				switch (subFsym.getName()) {
				case "concat": {
					// length beider argumente,
					final int rhsSize = Integer.parseInt(subTerm.getParameters()[1].getSort().getIndices()[0]);
					if (upperIndex > rhsSize - 1) {
						if (lowerIndex > rhsSize - 1) {
							// selecting from lhs of concat

							final String[] selectIndices = new String[2];
							selectIndices[0] = String.valueOf(upperIndex - rhsSize);
							selectIndices[1] = String.valueOf(lowerIndex - rhsSize);

							final FunctionSymbol extract = mTheory.getFunctionWithResult("extract", selectIndices, null,
									subTerm.getParameters()[0].getSort());
							if (isConstRelation(subTerm.getParameters()[0], null)) {
								return simplifySelectConst(extract, subTerm.getParameters()[0]);
							}
							return mTheory.term(extract, subTerm.getParameters()[0]);
						} else {
							// selecting from both sides of concat

							// select from lhs of concat
							final String[] selectIndices1 = new String[2];
							selectIndices1[0] = String.valueOf(upperIndex - rhsSize);
							selectIndices1[1] = "0";
							final FunctionSymbol extractLhs = mTheory.getFunctionWithResult("extract", selectIndices1,
									null, subTerm.getParameters()[0].getSort());

							// select from rhs of concat
							final String[] selectIndices2 = new String[2];
							selectIndices2[0] = String.valueOf(rhsSize - 1); // rhs size
							selectIndices2[1] = String.valueOf(lowerIndex);

							final FunctionSymbol extractRhs = mTheory.getFunctionWithResult("extract", selectIndices2,
									null, subTerm.getParameters()[1].getSort());
							Term selectLhs = mTheory.term(extractLhs, subTerm.getParameters()[0]);
							Term selectRhs = mTheory.term(extractRhs, subTerm.getParameters()[1]);
							if (isConstRelation(subTerm.getParameters()[0], null)) {
								selectLhs = simplifySelectConst(extractLhs, subTerm.getParameters()[0]);
							}
							if (isConstRelation(subTerm.getParameters()[1], null)) {
								selectRhs = simplifySelectConst(extractRhs, subTerm.getParameters()[1]);
							}
							return mTheory.term("concat", selectLhs, selectRhs);

						}

					} else {
						// selecting from rhs of concat
						final FunctionSymbol extract = mTheory.getFunctionWithResult("extract", fsym.getIndices(), null,
								subTerm.getParameters()[1].getSort());
						if (isConstRelation(subTerm.getParameters()[1], null)) {
							return simplifySelectConst(extract, subTerm.getParameters()[1]);
						}
						return mTheory.term(extract, subTerm.getParameters()[1]);
					}

				}
				case "extract": {
					// term[x : y][i : j] replaced by term[y + i + (i - j) : y + j]
					final int innerExtractLowerIndex = Integer.parseInt(subFsym.getIndices()[1]);
					final int difference = upperIndex - lowerIndex;
					final String[] selectIndices = new String[2];
					selectIndices[0] = String.valueOf(lowerIndex + innerExtractLowerIndex + difference);
					selectIndices[1] = String.valueOf(lowerIndex + innerExtractLowerIndex);
					final FunctionSymbol extract = mTheory.getFunctionWithResult("extract", selectIndices, null,
							subTerm.getParameters()[0].getSort());
					if (isConstRelation(subTerm.getParameters()[0], null)) {
						return simplifySelectConst(extract, subTerm.getParameters()[0]);
					}
					return mTheory.term(extract, subTerm.getParameters()[0]);

				}
				case "bvand": {
					assert subTerm.getParameters().length == 2;
					return mTheory.term("bvand", mTheory.term(fsym, subTerm.getParameters()[0]),
							mTheory.term(fsym, subTerm.getParameters()[1]));
				}
				case "bvor": {
					assert subTerm.getParameters().length == 2;
					return mTheory.term("bvor", mTheory.term(fsym, subTerm.getParameters()[0]),
							mTheory.term(fsym, subTerm.getParameters()[1]));
				}
				case "bvnot": {
					assert subTerm.getParameters().length == 1;
					return mTheory.term("bvnot", mTheory.term(fsym, subTerm.getParameters()[0]));

				}
				default: {
					if (isConstRelation(param, null)) {
						return simplifySelectConst(fsym, param);
					}
					return mTheory.term(fsym, param);
				}
				}

			}
		}
		if (isConstRelation(param, null)) {
			return simplifySelectConst(fsym, param);
		}
		return mTheory.term(fsym, param);

	}

	/**
	 * iterates over a formula of form (not (or (not (= b a)) (not (= a c)))) often
	 * provided by mUtils.convertEq (called in TermCompiler)
	 */
	public Term iterateOverBvEqualites(final Term convertedEquality) {
		// System.out.println(convertedEquality.toStringDirect());
		if (convertedEquality.equals(mTheory.mTrue) || convertedEquality.equals(mTheory.mFalse)) {
			return convertedEquality;
		}
		assert convertedEquality instanceof ApplicationTerm;
		final ApplicationTerm equalities = (ApplicationTerm) convertedEquality;

		if (equalities.getFunction().getName().equals("not")) {
			// called if the input formula is of form (= a b c ...)
			final ApplicationTerm disjunction = (ApplicationTerm) equalities.getParameters()[0];
			final Term[] orderedDisjTerms = new Term[disjunction.getParameters().length];
			for (int i = 0; i < disjunction.getParameters().length; i++) {
				final Term para = disjunction.getParameters()[i];
				assert para instanceof ApplicationTerm;
				final ApplicationTerm apPara = (ApplicationTerm) para;
				assert apPara.getFunction().getName().equals("not");

				orderedDisjTerms[i] = simplifyBinaryBitVecEquality(apPara.getParameters()[0]);
			}
			final Term result = mTheory.not(mTheory.or(orderedDisjTerms));
			// System.out.println(result.toStringDirect());
			return result;
		} else if (equalities.getFunction().getName().equals("=")) {
			assert equalities.getParameters().length == 2; // if false, call mUtils.convertEq first
			final Term simpAndOrder = simplifyBinaryBitVecEquality(equalities);
			return simpAndOrder;
		} else {
			throw new UnsupportedOperationException("Not an Equality");
		}

	}

	/**
	 * Input is a binary equality.
	 *
	 * Simplifies trivial equalities. calls orderParameters,
	 * eliminateConcatPerfectMatch and eliminateConcatNoMatch
	 *
	 * Retruns true, false, an equality or a mUtils.convertAnd() of two equalities
	 **/
	private Term simplifyBinaryBitVecEquality(final Term equality) {
		ApplicationTerm appterm;
		if (equality instanceof ApplicationTerm) {
			appterm = (ApplicationTerm) equality;
		} else if (equality instanceof AnnotatedTerm) {
			final AnnotatedTerm convAnno = (AnnotatedTerm) equality;
			appterm = (ApplicationTerm) convAnno.getSubterm();
		} else {
			throw new UnsupportedOperationException("Not an Equality");
		}
		if (equality.equals(mTheory.mTrue) || equality.equals(mTheory.mFalse)) {
			return equality;
		}
		assert appterm.getFunction().getName().equals("=");
		appterm = (ApplicationTerm) orderParameters(appterm.getFunction(), appterm.getParameters());
		final Term lhs = appterm.getParameters()[0];
		final Term rhs = appterm.getParameters()[1];

		if (lhs.equals(rhs)) {
			return mTheory.mTrue;
		}
		if (isConstRelation(lhs, rhs)) {
			if (parseBitvectorConstant(lhs).equals(parseBitvectorConstant(rhs))) {
				return mTheory.mTrue;
			} else {
				return mTheory.mFalse;
			}
		}
		final Term perfectMatch = eliminateConcatPerfectMatch(appterm.getFunction(), lhs, rhs);
		if (perfectMatch != null) {
			if (((ApplicationTerm) perfectMatch).getFunction().getName().equals("and")) {
				// Needs to be converted for iterateOverBvEqualities
				return mUtils.convertAnd(perfectMatch);
			} else {
				return perfectMatch;
			}
		}
		final Term noMatch = eliminateConcatNoMatch(appterm.getFunction(), lhs, rhs);
		if (noMatch != null) {
			if (((ApplicationTerm) noMatch).getFunction().getName().equals("and")) {
				return mUtils.convertAnd(noMatch);
			} else {
				return noMatch;
			}
		}
		return equality;
	}

	/**
	 * orders the parameter of input Term, if its a symmetric operand. Optimization
	 * for two cases: Case1: bvadd(a,b) = bvadd(b,a) ordered to bvadd(a,b) =
	 * bvadd(a,b) and can later be replaced by true Case2: In a more complex Term,
	 * bitblasting for bvadd(a,b) is only applied once. Otherwise we would bitblast
	 * twice, for bvadd(a,b) and bvadd(b,a). =, bvadd, bvmul, bvor, bvand
	 */
	public Term orderParameters(final FunctionSymbol fsym, final Term[] params) {
		assert params[0].getSort().isBitVecSort();
		assert params.length == 2;
		assert fsym.getName().equals("=") || fsym.getName().equals("bvadd") || fsym.getName().equals("bvmul")
				|| fsym.getName().equals("bvand") || fsym.getName().equals("bvor"); // has to be a symetricFunction
		if (params[0].hashCode() < params[1].hashCode()) {
			return mTheory.term(fsym, params);
		} else if (params[0].hashCode() > params[1].hashCode()) {
			return mTheory.term(fsym, params[1], params[0]);
		} else {
			return mTheory.term(fsym, params);
		}
	}

	public Term transformBvcomp(final Term[] params) {
		// bit comparator: equals #b1 iff all bits are equal
		final Sort bvSort1 = mTheory.getSort(SMTLIBConstants.BITVEC, new String[] { "1" });
		return mTheory.term("ite", mTheory.term("=", params[0], params[1]), mTheory.constant(BigInteger.ONE, bvSort1),
				mTheory.constant(BigInteger.ZERO, bvSort1));
	}

	public Term transformBvsdiv(final Term[] params) {
		final String[] indices = new String[2];
		indices[0] = String.valueOf(Integer.valueOf(params[0].getSort().getIndices()[0]) - 1);
		indices[1] = String.valueOf(Integer.valueOf(params[0].getSort().getIndices()[0]) - 1);
		final Term msbLhs = mTheory.term("extract", indices, null, params[0]);
		final Term msbRhs = mTheory.term("extract", indices, null, params[1]);

		final Term zeroVec = mTheory.binary("#b0");
		final Term oneVec =  mTheory.binary("#b1");

		final Term ifterm1 = mTheory.and(  mTheory.term( "=",zeroVec, msbLhs),
				 mTheory.term( "=", zeroVec, msbRhs));
		final Term ifterm2 = mTheory.and(  mTheory.term( "=",oneVec, msbLhs),
				 mTheory.term( "=", zeroVec, msbRhs));
		final Term ifterm3 = mTheory.and( mTheory.term( "=", zeroVec, msbLhs),
				 mTheory.term( "=", oneVec, msbRhs));

		final Term bvudiv = mTheory.term( "bvudiv",  params);
		final Term thenTerm2 = mTheory.term( "bvneg",
				mTheory.term( "bvudiv",
						mTheory.term( "bvneg",  params[0]),
						params[1]));
		final Term thenTerm3 = mTheory.term("bvneg",
				mTheory.term("bvudiv", params[0],
						mTheory.term("bvneg",  params[1])));

		final Term elseTerm = mTheory.term( "bvudiv",
				mTheory.term( "bvneg", params[0]),
				mTheory.term( "bvneg", params[1]));

		final Term iteChain2 = mTheory.term("ite", ifterm3, thenTerm3, elseTerm);
		final Term iteChain1 = mTheory.term("ite", ifterm2, thenTerm2, iteChain2);
		final Term bvsdiv = mTheory.term("ite", ifterm1, bvudiv, iteChain1);

		return bvsdiv;
	}

	public Term transformBvsdivOld(final Term[] params) {

		// abbreviation as defined in the SMT-Lib
		final int size = Integer.parseInt(params[0].getSort().getIndices()[0]);
		final String[] selectIndices = new String[2];
		selectIndices[0] = String.valueOf(size - 1);
		selectIndices[1] = String.valueOf(size - 1);

		final FunctionSymbol extract = mTheory.getFunctionWithResult("extract", selectIndices.clone(), null,
				params[0].getSort());
		final Term extractSignLhs = mTheory.term(extract, params[0]);
		final Term extractSignRhs = mTheory.term(extract, params[1]);
		final String zeroVec = "#b" + new String(new char[size]).replace("\0", "0");
		final String oneVec = "#b" + new String(new char[size - 1]).replace("\0", "0") + "1";
		final Term rhsZero = mTheory.term("=", params[1], mTheory.binary(zeroVec));
		Term divZero;
		if (size > 1) {
			divZero = mTheory.ifthenelse(mTheory.term("=", extractSignLhs, mTheory.binary("#b0")), params[0],
					mTheory.binary(oneVec)); // first operand if positiv, otherwise 1 (int)
		} else {
			divZero = mTheory.binary("#b1");
		}

		final Term bvsdivAbbreviation = mTheory.ifthenelse(
				mTheory.term("and", mTheory.term("=", extractSignLhs, mTheory.binary("#b0")),
						mTheory.term("=", extractSignRhs, mTheory.binary("#b0"))),
				mTheory.term("bvudiv", params[0], params[1]),
				mTheory.ifthenelse(
						mTheory.term("and", mTheory.term("=", extractSignLhs, mTheory.binary("#b1")),
								mTheory.term("=", extractSignRhs, mTheory.binary("#b0"))),
						mTheory.term("bvneg", mTheory.term("bvudiv", mTheory.term("bvneg", params[0]), params[1])),
						mTheory.ifthenelse(
								mTheory.term("and", mTheory.term("=", extractSignLhs, mTheory.binary("#b0")),
										mTheory.term("=", extractSignRhs, mTheory.binary("#b1"))),
								mTheory.term("bvneg",
										mTheory.term("bvudiv", params[0], mTheory.term("bvneg", params[1]))),
								mTheory.term("bvudiv", mTheory.term("bvneg", params[0]),
										mTheory.term("bvneg", params[1])))));

		return mTheory.ifthenelse(rhsZero, divZero, bvsdivAbbreviation);
	}

	public Term transformBvsrem(final Term[] params) {
		// abbreviation as defined in the SMT-Lib
		final int size = Integer.parseInt(params[0].getSort().getIndices()[0]);
		final String[] selectIndices = new String[2];
		selectIndices[0] = String.valueOf(size - 1);
		selectIndices[1] = String.valueOf(size - 1);

		final FunctionSymbol extract = mTheory.getFunctionWithResult("extract", selectIndices.clone(), null,
				params[0].getSort());
		final Term extractSignLhs = mTheory.term(extract, params[0]);
		final Term extractSignRhs = mTheory.term(extract, params[1]);

		final Term definitionBvsrem = (mTheory.ifthenelse(
				mTheory.term("and", mTheory.term("=", extractSignLhs, mTheory.binary("#b0")),
						mTheory.term("=", extractSignRhs, mTheory.binary("#b0"))),
				mTheory.term("bvurem", params[0], params[1]),
				mTheory.ifthenelse(
						mTheory.term("and", mTheory.term("=", extractSignLhs, mTheory.binary("#b1")),
								mTheory.term("=", extractSignRhs, mTheory.binary("#b0"))),
						mTheory.term("bvneg", mTheory.term("bvurem", mTheory.term("bvneg", params[0]), params[1])),
						mTheory.ifthenelse(
								mTheory.term("and", mTheory.term("=", extractSignLhs, mTheory.binary("#b0")),
										mTheory.term("=", extractSignRhs, mTheory.binary("#b1"))),
								mTheory.term("bvurem", params[0], mTheory.term("bvneg", params[1])),
								mTheory.term("bvneg", mTheory.term("bvurem", mTheory.term("bvneg", params[0]),
										mTheory.term("bvneg", params[1])))))));
		return definitionBvsrem;
	}

	public Term transformBvsmod(final Term[] params) {
		// abbreviation as defined in the SMT-Lib
		final int size = Integer.parseInt(params[0].getSort().getIndices()[0]);
		final String[] selectIndices = new String[2];
		selectIndices[0] = String.valueOf(size - 1);
		selectIndices[1] = String.valueOf(size - 1);

		final FunctionSymbol extract = mTheory.getFunctionWithResult("extract", selectIndices.clone(), null,
				params[0].getSort());
		final Term extractSignLhs = mTheory.term(extract, params[0]);
		final Term extractSignRhs = mTheory.term(extract, params[1]);
		final Term ite1 = mTheory.ifthenelse(mTheory.term("=", extractSignLhs, mTheory.binary("#b0")), params[0],
				mTheory.term("bvneg", params[0]));
		final Term ite2 = mTheory.ifthenelse(mTheory.term("=", extractSignRhs, mTheory.binary("#b0")), params[1],
				mTheory.term("bvneg", params[1]));
		final Term bvurem = mTheory.term("bvurem", ite1, ite2);

		final Term zeroVec = mTheory.constant(BigInteger.ZERO, params[0].getSort());

		final Term elseTerm3 = mTheory.ifthenelse(
				mTheory.and(mTheory.term("=", extractSignLhs, mTheory.binary("#b0")),
						mTheory.term("=", extractSignRhs, mTheory.binary("#b1"))),
				mTheory.term("bvadd", bvurem, params[1]), mTheory.term("bvneg", bvurem));
		final Term elseTerm2 = mTheory.ifthenelse(
				mTheory.and(mTheory.term("=", extractSignLhs, mTheory.binary("#b1")),
						mTheory.term("=", extractSignRhs, mTheory.binary("#b0"))),
				mTheory.term("bvadd", mTheory.term("bvneg", bvurem), params[1]), elseTerm3);
		final Term elseTerm = mTheory.ifthenelse(mTheory.and(mTheory.term("=", extractSignLhs, mTheory.binary("#b0")),
				mTheory.term("=", extractSignRhs, mTheory.binary("#b0"))), bvurem, elseTerm2);

		// bvsmod by zero:
		final String zeroVec2 = "#b" + new String(new char[size]).replace("\0", "0");
		final Term rhsZero = mTheory.term("=", params[1], mTheory.binary(zeroVec2));
		return mTheory.ifthenelse(rhsZero, params[0],
				mTheory.ifthenelse(mTheory.term("=", bvurem, zeroVec), bvurem, elseTerm));
	}

	public Term transformBvashr(final Term[] params) {
		// abbreviation as defined in the SMT-Lib
		final int size = Integer.parseInt(params[0].getSort().getIndices()[0]);
		final String[] selectIndices = new String[2];
		selectIndices[0] = String.valueOf(size - 1);
		selectIndices[1] = String.valueOf(size - 1);

		final FunctionSymbol extract = mTheory.getFunctionWithResult("extract", selectIndices.clone(), null,
				params[0].getSort());

		return (mTheory.ifthenelse(mTheory.term("=", mTheory.term(extract, params[0]), mTheory.binary("#b0")),
				mTheory.term("bvlshr", params[0], params[1]),
				mTheory.term("bvnot", mTheory.term("bvlshr", mTheory.term("bvnot", params[0]), params[1]))));
	}

	public Term transformRepeat(final Term[] params, final FunctionSymbol fsym, final Term convertedApp) {
		if (fsym.getIndices()[0].equals("1")) {
			return (params[0]);

		} else {
			if (isConstRelation(params[0], null)) {
				final String constAsString = parseBitvectorConstant(params[0]).toString(2);
				String repeat = "#b" + constAsString;
				for (int i = 1; i < Integer.parseInt(fsym.getIndices()[0]); i++) { // start from 1
					repeat = repeat + constAsString;
				}
				return mTheory.binary(repeat);

			} else {
				Term repeat = params[0];
				for (int i = 1; i < Integer.parseInt(fsym.getIndices()[0]); i++) { // start from 1
					repeat =  mTheory.term("concat", repeat,  params[0]);
				}
				return repeat;

			}

		}

	}

	public Term transformSignExtend(final Term[] params, final FunctionSymbol fsym, final Term convertedApp) {
		if (fsym.getIndices()[0].equals("0")) {
			return params[0];
		} else {
			if (isConstRelation(params[0], null)) {
				String repeat = "#b";
				final String constAsString = parseBitvectorConstant(params[0]).toString(2);
				repeat = repeat + constAsString.charAt(0);
				for (int i = 1; i < Integer.parseInt(fsym.getIndices()[0]); i++) {
					repeat = repeat + constAsString.charAt(0);
				}
				return mTheory.binary(repeat + constAsString);

			}
			return convertedApp;
		}
	}

	public Term transformRotateleft(final Term[] params, final FunctionSymbol fsym, final Term convertedApp) {
		final int size = Integer.parseInt(params[0].getSort().getIndices()[0]);
		int rotationDistance = Integer.valueOf(fsym.getIndices()[0]);
		if (rotationDistance > size) {
			rotationDistance = (rotationDistance % size);
		}
		if (rotationDistance == 0) {
			return params[0];
		} else if (size == 1) {
			return params[0];
		} else {
			if (isConstRelation(params[0], null)) {
				final String constAsString = parseBitvectorConstant(params[0]).toString(2);
				final String overhead = (String) constAsString.subSequence(0, rotationDistance);
				final String shifted = (String) constAsString.subSequence(rotationDistance, constAsString.length());
				return mTheory.binary("#b" + shifted + overhead);

			} else {
				final String[] selectIndicesLhs = new String[2];
				selectIndicesLhs[0] = String.valueOf(size - 2);
				selectIndicesLhs[1] = String.valueOf(0);

				final String[] selectIndicesRhs = new String[2];
				selectIndicesRhs[0] = String.valueOf(size - 1);
				selectIndicesRhs[1] = String.valueOf(size - 1);

				final String[] rotateIndices = new String[1];
				rotateIndices[0] = String.valueOf(rotationDistance - 1);

				final FunctionSymbol extractLhs =
						mTheory.getFunctionWithResult("extract", selectIndicesLhs, null, params[0].getSort());
				final FunctionSymbol extractRhs =
						mTheory.getFunctionWithResult("extract", selectIndicesRhs, null, params[0].getSort());
				final FunctionSymbol rotateOneLess = mTheory.getFunctionWithResult("rotate_left", rotateIndices, null,
						params[0].getSort());

				final Term concat = mTheory.term("concat", mTheory.term(extractLhs, params[0]),
						mTheory.term(extractRhs, params[0]));

				return mTheory.term(rotateOneLess, concat);
			}

		}
	}



	public Term transformRotateright(final Term[] params, final FunctionSymbol fsym, final Term convertedApp) {
		final int size = Integer.parseInt(params[0].getSort().getIndices()[0]);
		int rotationDistance = Integer.valueOf(fsym.getIndices()[0]);
		if (rotationDistance > size) {
			rotationDistance = (rotationDistance % size);
		}
		if (rotationDistance == 0) {
			return params[0];

		} else if (size == 1) {
			return params[0];
		} else {
			if (isConstRelation(params[0], null)) {
				final String constAsString = parseBitvectorConstant(params[0]).toString(2);
				final String shifted = (String) constAsString.subSequence(0,
						(constAsString.length() - rotationDistance));
				final String overhead = (String) constAsString.subSequence((constAsString.length() - rotationDistance),
						constAsString.length());
				return mTheory.binary("#b" + overhead + shifted);

			} else {
				final String[] selectIndicesLhs = new String[2];
				selectIndicesLhs[0] = String.valueOf(0);
				selectIndicesLhs[1] = String.valueOf(0);

				final String[] selectIndicesRhs = new String[2];
				selectIndicesRhs[0] = String.valueOf(size - 1);
				selectIndicesRhs[1] = String.valueOf(1);

				final String[] rotateIndices = new String[1];
				rotateIndices[0] = String.valueOf(rotationDistance - 1);

				final FunctionSymbol extractLhs =
						mTheory.getFunctionWithResult("extract", selectIndicesLhs, null, params[0].getSort());
				final FunctionSymbol extractRhs =
						mTheory.getFunctionWithResult("extract", selectIndicesRhs, null, params[0].getSort());
				final FunctionSymbol rotateOneLess =
						mTheory.getFunctionWithResult("rotate_left", rotateIndices, null, params[0].getSort());

				final Term concat = mTheory.term("concat", mTheory.term(extractLhs, params[0]),
						mTheory.term(extractRhs, params[0]));

				return mTheory.term(rotateOneLess, concat);
			}

		}
	}

	public Term transformBvnot(final Term[] params, final FunctionSymbol fsym, final Term convertedApp) {
		if (isConstRelation(params[0], null)) {
			return simplifyNotConst(fsym, params[0]);
		}
		return convertedApp;
	}

	public Term transformBvneg(final Term[] params, final FunctionSymbol fsym, final Term convertedApp) {
		if (isConstRelation(params[0], null)) {
			return simplifyNegConst(fsym, params[0]);
		}
		final int size = Integer.valueOf(convertedApp.getSort().getIndices()[0]);
		final String repeated = new String(new char[size - 1]).replace("\0", "0");
		final String oneVec = "#b" + repeated + "1";
		final Term bvneg = mTheory.term("bvadd", mTheory.term("bvnot", params[0]), mTheory.binary(oneVec));

		return bvneg;
	}

	public Term transformBvxor(final Term[] params) {
		// (bvxor s t) abbreviates (bvor (bvand s (bvnot t)) (bvand (bvnot s) t))
		// bvxor is left associative
		assert params.length == 2;
		return mTheory.term("bvor", mTheory.term("bvand", params[0], mTheory.term("bvnot", params[1])),
				mTheory.term("bvand", mTheory.term("bvnot", params[0]), params[1]));

	}

	public Term transformBvxnor(final Term[] params) {
		// (bvxnor s t) abbreviates (bvor (bvand s t) (bvand (bvnot s) (bvnot t)))
		// bvxor is left associative
		assert params.length == 2;
		return mTheory.term("bvor", mTheory.term("bvand", params[0], params[1]),
				mTheory.term("bvand", mTheory.term("bvnot", params[0]), mTheory.term("bvnot", params[1])));

	}

	public Term transformExtract(final Term[] params, final FunctionSymbol fsym) {
		if (isConstRelation(params[0], null)) {
			return simplifySelectConst(fsym, params[0]);
		}
		final Term extract = propagateExtract(fsym, params[0]);
		return extract;

	}

	public Term transformBvult(final Term[] params, final FunctionSymbol fsym, final Term convertedApp) {
		final Term bvult = getBvultTerm(convertedApp);
		if (bvult instanceof ApplicationTerm) {
			final ApplicationTerm appterm = (ApplicationTerm) bvult;
			if (appterm.getFunction().getName().equals("or")) {
				return mUtils.convertOr(bvult);

			}
		}
		return bvult;

	}

	public Term transformConcat(final Term[] params, final FunctionSymbol fsym, final Term convertedApp) {
		if (isConstRelation(params[0], params[1])) {
			return simplifyConcatConst(fsym, params[0], params[1]);
		}
		return convertedApp;
	}

	public Term transformBvArithmetic(final Term[] params, final FunctionSymbol fsym, final Term convertedApp) {
		if (isConstRelation(params[0], params[1])) {
			return simplifyBitvectorConstantOp(fsym, params[0], params[1]);
		}
		return convertedApp;
	}

	public Term transformBvaddBvmul(final Term[] params, final FunctionSymbol fsym) {
		if (isConstRelation(params[0], params[1])) {
			return simplifyBitvectorConstantOp(fsym, params[0], params[1]);
		}
		// Order Parameters
		return orderParameters(fsym, params);
	}

	public Term transformBitwise(final Term[] params, final FunctionSymbol fsym) {
		assert params.length == 2;
		if (isConstRelation(params[0], params[1])) {
			return simplifyBitvectorConstantOp(fsym, params[0], params[1]);
		} else {
			final Term bitMask = bitMaskElimination(orderParameters(fsym, params));
			return bitMask;
		}
	}

	public Term transformShift(final Term[] params, final FunctionSymbol fsym, final Term convertedApp) {
		if (isConstRelation(params[0], params[1])) {
			return simplifyShiftConst(fsym, params[0], params[1]);

		}
		return convertedApp;
	}

	public Term transformInequality(final Term[] params, final FunctionSymbol fsym, final Term convertedApp) {
		final Term bvult = getBvultTerm(convertedApp);
		if (bvult instanceof ApplicationTerm) {
			final ApplicationTerm appterm = (ApplicationTerm) bvult;
			if (appterm.getFunction().getName().equals("or")) {
				return mUtils.convertOr(bvult);
			}
		}
		return bvult;
	}
}