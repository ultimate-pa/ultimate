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

import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class BvUtils {

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
		final Theory theory = sort.getTheory();
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
			final Term bitString = theory.binary("#b" + value);
			assert bitString.getSort().equals(sort);
			return theory.binary("#b" + value);
		}
		throw new UnsupportedOperationException("Can't convert bv constant: " + fsym.getName());
	}
	/*
	 * bvadd, bvudiv, bvmul
	 */
	public Term simplifyBitvectorConstantOp(final FunctionSymbol fsym, final Term lhs, final Term rhs) {
		final Theory theory = lhs.getTheory();
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
		return theory.constant(result, fsym.getReturnSort());
	}


	public Term transformBvcomp(final Term[] params) {
		final Theory theory = params[0].getTheory();
		// bit comparator: equals #b1 iff all bits are equal
		final Sort bvSort1 = theory.getSort(SMTLIBConstants.BITVEC, new String[] { "1" });
		return theory.term("ite", theory.term("=", params[0], params[1]), theory.constant(BigInteger.ONE, bvSort1),
				theory.constant(BigInteger.ZERO, bvSort1));
	}

	public Term transformBvsdiv(final Term[] params) {
		final Theory theory = params[0].getTheory();
		final String[] indices = new String[2];
		indices[0] = String.valueOf(Integer.valueOf(params[0].getSort().getIndices()[0]) - 1);
		indices[1] = String.valueOf(Integer.valueOf(params[0].getSort().getIndices()[0]) - 1);
		final Term msbLhs = theory.term("extract", indices, null, params[0]);
		final Term msbRhs = theory.term("extract", indices, null, params[1]);

		final Term zeroVec = theory.binary("#b0");
		final Term oneVec = theory.binary("#b1");

		final Term ifterm1 = theory.and(theory.term("=", zeroVec, msbLhs), theory.term("=", zeroVec, msbRhs));
		final Term ifterm2 = theory.and(theory.term("=", oneVec, msbLhs), theory.term("=", zeroVec, msbRhs));
		final Term ifterm3 = theory.and(theory.term("=", zeroVec, msbLhs), theory.term("=", oneVec, msbRhs));

		final Term bvudiv = theory.term("bvudiv", params);
		final Term thenTerm2 = theory.term("bvneg", theory.term("bvudiv", theory.term("bvneg", params[0]), params[1]));
		final Term thenTerm3 = theory.term("bvneg", theory.term("bvudiv", params[0], theory.term("bvneg", params[1])));

		final Term elseTerm = theory.term("bvudiv", theory.term("bvneg", params[0]), theory.term("bvneg", params[1]));

		final Term iteChain2 = theory.term("ite", ifterm3, thenTerm3, elseTerm);
		final Term iteChain1 = theory.term("ite", ifterm2, thenTerm2, iteChain2);
		final Term bvsdiv = theory.term("ite", ifterm1, bvudiv, iteChain1);

		return bvsdiv;
	}

	public Term transformBvsrem(final Term[] params) {
		final Theory theory = params[0].getTheory();
		// abbreviation as defined in the SMT-Lib
		final int size = Integer.parseInt(params[0].getSort().getIndices()[0]);
		final String[] selectIndices = new String[2];
		selectIndices[0] = String.valueOf(size - 1);
		selectIndices[1] = String.valueOf(size - 1);

		final FunctionSymbol extract = theory.getFunctionWithResult("extract", selectIndices.clone(), null,
				params[0].getSort());
		final Term extractSignLhs = theory.term(extract, params[0]);
		final Term extractSignRhs = theory.term(extract, params[1]);

		final Term definitionBvsrem = (theory.ifthenelse(
				theory.term("and", theory.term("=", extractSignLhs, theory.binary("#b0")),
						theory.term("=", extractSignRhs, theory.binary("#b0"))),
				theory.term("bvurem", params[0], params[1]),
				theory.ifthenelse(
						theory.term("and", theory.term("=", extractSignLhs, theory.binary("#b1")),
								theory.term("=", extractSignRhs, theory.binary("#b0"))),
						theory.term("bvneg", theory.term("bvurem", theory.term("bvneg", params[0]), params[1])),
						theory.ifthenelse(
								theory.term("and", theory.term("=", extractSignLhs, theory.binary("#b0")),
										theory.term("=", extractSignRhs, theory.binary("#b1"))),
								theory.term("bvurem", params[0], theory.term("bvneg", params[1])),
								theory.term("bvneg", theory.term("bvurem", theory.term("bvneg", params[0]),
										theory.term("bvneg", params[1])))))));
		return definitionBvsrem;
	}

	public Term transformBvsmod(final Term[] params) {
		final Theory theory = params[0].getTheory();
		// abbreviation as defined in the SMT-Lib
		final int size = Integer.parseInt(params[0].getSort().getIndices()[0]);
		final String[] selectIndices = new String[2];
		selectIndices[0] = String.valueOf(size - 1);
		selectIndices[1] = String.valueOf(size - 1);

		final FunctionSymbol extract = theory.getFunctionWithResult("extract", selectIndices.clone(), null,
				params[0].getSort());
		final Term extractSignLhs = theory.term(extract, params[0]);
		final Term extractSignRhs = theory.term(extract, params[1]);
		final Term ite1 = theory.ifthenelse(theory.term("=", extractSignLhs, theory.binary("#b0")), params[0],
				theory.term("bvneg", params[0]));
		final Term ite2 = theory.ifthenelse(theory.term("=", extractSignRhs, theory.binary("#b0")), params[1],
				theory.term("bvneg", params[1]));
		final Term bvurem = theory.term("bvurem", ite1, ite2);

		final Term zeroVec = theory.constant(BigInteger.ZERO, params[0].getSort());

		final Term elseTerm3 = theory.ifthenelse(
				theory.and(theory.term("=", extractSignLhs, theory.binary("#b0")),
						theory.term("=", extractSignRhs, theory.binary("#b1"))),
				theory.term("bvadd", bvurem, params[1]), theory.term("bvneg", bvurem));
		final Term elseTerm2 = theory.ifthenelse(
				theory.and(theory.term("=", extractSignLhs, theory.binary("#b1")),
						theory.term("=", extractSignRhs, theory.binary("#b0"))),
				theory.term("bvadd", theory.term("bvneg", bvurem), params[1]), elseTerm3);
		final Term elseTerm = theory.ifthenelse(theory.and(theory.term("=", extractSignLhs, theory.binary("#b0")),
				theory.term("=", extractSignRhs, theory.binary("#b0"))), bvurem, elseTerm2);

		// bvsmod by zero:
		final String zeroVec2 = "#b" + new String(new char[size]).replace("\0", "0");
		final Term rhsZero = theory.term("=", params[1], theory.binary(zeroVec2));
		return theory.ifthenelse(rhsZero, params[0],
				theory.ifthenelse(theory.term("=", bvurem, zeroVec), bvurem, elseTerm));
	}

	public Term transformBvashr(final Term[] params) {
		final Theory theory = params[0].getTheory();
		// abbreviation as defined in the SMT-Lib
		final int size = Integer.parseInt(params[0].getSort().getIndices()[0]);
		final String[] selectIndices = new String[2];
		selectIndices[0] = String.valueOf(size - 1);
		selectIndices[1] = String.valueOf(size - 1);

		final FunctionSymbol extract = theory.getFunctionWithResult("extract", selectIndices.clone(), null,
				params[0].getSort());

		return (theory.ifthenelse(theory.term("=", theory.term(extract, params[0]), theory.binary("#b0")),
				theory.term("bvlshr", params[0], params[1]),
				theory.term("bvnot", theory.term("bvlshr", theory.term("bvnot", params[0]), params[1]))));
	}

	public Term transformRotateleft(final Term[] params, final FunctionSymbol fsym, final Term convertedApp) {
		final Theory theory = convertedApp.getTheory();
		final int size = Integer.parseInt(params[0].getSort().getIndices()[0]);
		final int rotationDistance = Integer.valueOf(fsym.getIndices()[0]) % size;
		if (rotationDistance == 0) {
			return params[0];
		} else {
			final String[] selectIndicesLhs = new String[2];
			selectIndicesLhs[0] = String.valueOf(size - rotationDistance - 1);
			selectIndicesLhs[1] = String.valueOf(0);

			final String[] selectIndicesRhs = new String[2];
			selectIndicesRhs[0] = String.valueOf(size - 1);
			selectIndicesRhs[1] = String.valueOf(size - rotationDistance);

			final FunctionSymbol extractLhs = theory.getFunctionWithResult("extract", selectIndicesLhs, null,
					params[0].getSort());
			final FunctionSymbol extractRhs = theory.getFunctionWithResult("extract", selectIndicesRhs, null,
					params[0].getSort());

			return theory.term("concat", theory.term(extractLhs, params[0]),
					theory.term(extractRhs, params[0]));
		}
	}

	public Term transformRotateright(final Term[] params, final FunctionSymbol fsym, final Term convertedApp) {
		final Theory theory = convertedApp.getTheory();
		final int size = Integer.parseInt(params[0].getSort().getIndices()[0]);
		final int rotationDistance = Integer.valueOf(fsym.getIndices()[0]) % size;
		if (rotationDistance == 0) {
			return params[0];
		} else {
			final String[] selectIndicesLhs = new String[2];
			selectIndicesLhs[0] = String.valueOf(rotationDistance - 1);
			selectIndicesLhs[1] = String.valueOf(0);

			final String[] selectIndicesRhs = new String[2];
			selectIndicesRhs[0] = String.valueOf(size - 1);
			selectIndicesRhs[1] = String.valueOf(rotationDistance);

			final FunctionSymbol extractLhs = theory.getFunctionWithResult("extract", selectIndicesLhs, null,
					params[0].getSort());
			final FunctionSymbol extractRhs = theory.getFunctionWithResult("extract", selectIndicesRhs, null,
					params[0].getSort());

			return theory.term("concat", theory.term(extractLhs, params[0]),
					theory.term(extractRhs, params[0]));
		}
	}

	public Term transformBvxor(final Term[] params) {
		// (bvxor s t) abbreviates (bvor (bvand s (bvnot t)) (bvand (bvnot s) t))
		// bvxor is left associative
		assert params.length == 2;
		final Theory theory = params[0].getTheory();
		return theory.term("bvor", theory.term("bvand", params[0], theory.term("bvnot", params[1])),
				theory.term("bvand", theory.term("bvnot", params[0]), params[1]));

	}

	public Term transformBvxnor(final Term[] params) {
		// (bvxnor s t) abbreviates (bvor (bvand s t) (bvand (bvnot s) (bvnot t)))
		// bvxor is left associative
		assert params.length == 2;
		final Theory theory = params[0].getTheory();
		return theory.term("bvor", theory.term("bvand", params[0], params[1]),
				theory.term("bvand", theory.term("bvnot", params[0]), theory.term("bvnot", params[1])));

	}
}