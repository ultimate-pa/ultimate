/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.math.BigInteger;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant.SupportedBitvectorOperations;

/**
 * Provides auxiliary methods for SMT bitvectors.
 *
 * @author Matthias Heizmann
 *
 */
public final class BitvectorUtils {

	private BitvectorUtils() {
		// Prevent instantiation of this utility class
	}

	private final static String BITVEC_CONST_PATTERN = "bv\\d+";

	public static boolean isBitvectorConstant(final FunctionSymbol symb) {
		return symb.isIntern() && symb.getName().matches(BITVEC_CONST_PATTERN);
	}

	/**
	 * @return true iff term is some bitvector constant (we do not care about the index) whose value is the input
	 *         number.
	 */
	public static boolean isBitvectorConstant(final BigInteger number, final Term term) {
		final BitvectorConstant bvConst = constructBitvectorConstant(term);
		if (bvConst == null) {
			return false;
		}
		return bvConst.getValue().equals(number);
	}

	/**
	 * Convert term to {@link BitvectorConstant} object. Return a {@link BitvectorConstant} object for term if
	 *
	 * @param term
	 * @return {@link BitvectorConstant} object that represents term if term is a bitvector literal otherwise null is
	 *         returned.
	 */
	public static BitvectorConstant constructBitvectorConstant(final Term term) {
		if (term instanceof ApplicationTerm) {
			if (SmtSortUtils.isBitvecSort(term.getSort())) {
				if (term.getSort().getIndices().length == 1) {
					final ApplicationTerm appTerm = (ApplicationTerm) term;
					final FunctionSymbol symb = appTerm.getFunction();
					if (isBitvectorConstant(symb)) {
						assert (symb.getName().startsWith("bv"));
						final String valueString = symb.getName().substring(2);
						final BigInteger value = new BigInteger(valueString);
						final BigInteger index = term.getSort().getIndices()[0];
						return new BitvectorConstant(value, index);
					}
				}
			}
		}
		return null;
	}

	/**
	 * @return Term that represents bitvector (value % 2^index)
	 */
	public static Term constructTerm(final Script script, final BigInteger value, final Sort sort) {
		final BigInteger index = sort.getIndices()[0];
		return constructTerm(script, new BitvectorConstant(value, index));
	}

	public static Term constructTerm(final Script script, final BitvectorConstant bitvec) {
		final String funcname = "bv" + bitvec.getValue().toString();
		return script.term(funcname, new BigInteger[] { bitvec.getIndex() }, null, new Term[0]);
	}

	public static boolean allTermsAreBitvectorConstants(final Term[] terms) {
		for (final Term term : terms) {
			if (!SmtSortUtils.isBitvecSort(term.getSort())) {
				return false;
			}
			if (term instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				if (isBitvectorConstant(appTerm.getFunction())) {
					continue;
				}
				return false;
			}
			return false;
		}
		return true;
	}

	public static Term termWithLocalSimplification(final Script script, final String funcname,
			final BigInteger[] indices, final Term... params) {
		final Term result;
		final SupportedBitvectorOperations bvop = SupportedBitvectorOperations.valueOf(funcname);
		switch (bvop) {
		case zero_extend:
			result = new Zero_extend().simplifiedResult(script, funcname, indices, params);
			break;
		case extract:
			result = new Extract().simplifiedResult(script, funcname, indices, params);
			break;
		case bvadd:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvadd(x, y))
					.simplifiedResult(script, funcname, indices, params);
			break;
		case bvsub:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvsub(x, y))
					.simplifiedResult(script, funcname, indices, params);
			break;
		case bvudiv:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvudiv(x, y))
					.simplifiedResult(script, funcname, indices, params);
			break;
		case bvurem:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvurem(x, y))
					.simplifiedResult(script, funcname, indices, params);
			break;
		case bvsdiv:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvsdiv(x, y))
					.simplifiedResult(script, funcname, indices, params);
			break;
		case bvsrem:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvsrem(x, y))
					.simplifiedResult(script, funcname, indices, params);
			break;
		case bvmul:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvmul(x, y))
					.simplifiedResult(script, funcname, indices, params);
			break;
		case bvand:
			result = new Bvand().simplifiedResult(script, funcname, indices, params);
			break;
		case bvor:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvor(x, y))
					.simplifiedResult(script, funcname, indices, params);
			break;
		case bvxor:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvxor(x, y))
					.simplifiedResult(script, funcname, indices, params);
			break;
		case bvnot:
			result = new Bvnot().simplifiedResult(script, funcname, indices, params);
			break;
		case bvneg:
			result = new Bvneg().simplifiedResult(script, funcname, indices, params);
			break;
		case bvshl:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvshl(x, y))
					.simplifiedResult(script, funcname, indices, params);
			break;
		case bvlshr:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvlshr(x, y))
					.simplifiedResult(script, funcname, indices, params);
			break;
		case bvashr:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvashr(x, y))
					.simplifiedResult(script, funcname, indices, params);
			break;
		case bvult:
			result = new RegularBitvectorOperation_BooleanResult(funcname, x -> y -> BitvectorConstant.bvult(x, y))
					.simplifiedResult(script, funcname, indices, params);
			break;
		case bvule:
			result = new RegularBitvectorOperation_BooleanResult(funcname, x -> y -> BitvectorConstant.bvule(x, y))
					.simplifiedResult(script, funcname, indices, params);
			break;
		case bvugt:
			result = new RegularBitvectorOperation_BooleanResult(funcname, x -> y -> BitvectorConstant.bvugt(x, y))
					.simplifiedResult(script, funcname, indices, params);
			break;
		case bvuge:
			result = new RegularBitvectorOperation_BooleanResult(funcname, x -> y -> BitvectorConstant.bvuge(x, y))
					.simplifiedResult(script, funcname, indices, params);
			break;
		case bvslt:
			result = new RegularBitvectorOperation_BooleanResult(funcname, x -> y -> BitvectorConstant.bvslt(x, y))
					.simplifiedResult(script, funcname, indices, params);
			break;
		case bvsle:
			result = new RegularBitvectorOperation_BooleanResult(funcname, x -> y -> BitvectorConstant.bvsle(x, y))
					.simplifiedResult(script, funcname, indices, params);
			break;
		case bvsgt:
			result = new RegularBitvectorOperation_BooleanResult(funcname, x -> y -> BitvectorConstant.bvsgt(x, y))
					.simplifiedResult(script, funcname, indices, params);
			break;
		case bvsge:
			result = new RegularBitvectorOperation_BooleanResult(funcname, x -> y -> BitvectorConstant.bvsge(x, y))
					.simplifiedResult(script, funcname, indices, params);
			break;

		default:
			if (BitvectorUtils.allTermsAreBitvectorConstants(params)) {
				throw new AssertionError("wasted optimization " + funcname);
			}
			result = script.term(funcname, indices, null, params);
			break;
		}
		return result;
	}

	private static abstract class BitvectorOperation {

		public final Term simplifiedResult(final Script script, final String funcname, final BigInteger[] indices,
				final Term... params) {
			assert getFunctionName().equals(funcname) : "wrong function name";
			assert getNumberOfIndices() == 0 && indices == null
					|| getNumberOfIndices() == indices.length : "wrong number of indices";
			assert getNumberOfParams() == params.length : "wrong number of params";
			final BitvectorConstant[] bvs = new BitvectorConstant[params.length];
			boolean allConstant = true;
			for (int i = 0; i < params.length; i++) {
				bvs[i] = constructBitvectorConstant(params[i]);
				allConstant &= (bvs[i] != null);
			}
			if (allConstant) {
				return simplify_ConstantCase(script, indices, bvs);
			}
			return simplify_NonConstantCase(script, indices, params, bvs);
		}

		protected Term simplify_NonConstantCase(final Script script, final BigInteger[] indices, final Term[] params,
				final BitvectorConstant[] bvs) {
			return notSimplified(script, indices, params);
		}

		private final Term notSimplified(final Script script, final BigInteger[] indices, final Term[] params) {
			return script.term(getFunctionName(), indices, null, params);
		}

		public abstract String getFunctionName();

		public abstract int getNumberOfIndices();

		public abstract int getNumberOfParams();

		public abstract Term simplify_ConstantCase(Script script, BigInteger[] indices, BitvectorConstant[] bvs);
	}

	private static class Extract extends BitvectorOperation {

		@Override
		public String getFunctionName() {
			return "extract";
		}

		@Override
		public int getNumberOfIndices() {
			return 2;
		}

		@Override
		public int getNumberOfParams() {
			return 1;
		}

		@Override
		public Term simplify_ConstantCase(final Script script, final BigInteger[] indices,
				final BitvectorConstant[] bvs) {
			final BitvectorConstant bv =
					BitvectorConstant.extract(bvs[0], indices[0].intValueExact(), indices[1].intValueExact());
			return constructTerm(script, bv);
		}

	}

	private static class Zero_extend extends BitvectorOperation {

		@Override
		public String getFunctionName() {
			return "zero_extend";
		}

		@Override
		public int getNumberOfIndices() {
			return 1;
		}

		@Override
		public int getNumberOfParams() {
			return 1;
		}

		@Override
		public Term simplify_ConstantCase(final Script script, final BigInteger[] indices,
				final BitvectorConstant[] bvs) {
			final BitvectorConstant bv = BitvectorConstant.zero_extend(bvs[0], indices[0]);
			return constructTerm(script, bv);
		}

	}

	private static abstract class RegularBitvectorOperation extends BitvectorOperation {

		@Override
		public int getNumberOfIndices() {
			return 0;
		}

		@Override
		public int getNumberOfParams() {
			return 2;
		}

	}

	private static class RegularBitvectorOperation_BitvectorResult extends RegularBitvectorOperation {

		private final String mName;
		private final Function<BitvectorConstant, Function<BitvectorConstant, BitvectorConstant>> mConstantSimplification;

		public RegularBitvectorOperation_BitvectorResult(final String name,
				final Function<BitvectorConstant, Function<BitvectorConstant, BitvectorConstant>> function) {
			super();
			mName = name;
			mConstantSimplification = function;
		}

		@Override
		public String getFunctionName() {
			return mName;
		}

		@Override
		public Term simplify_ConstantCase(final Script script, final BigInteger[] indices,
				final BitvectorConstant[] bvs) {
			if (bvs.length != getNumberOfParams()) {
				throw new AssertionError("supported and provided parameters differ - feature not yet implemented");
			}
			return constructTerm(script, mConstantSimplification.apply(bvs[0]).apply(bvs[1]));
		}
	}

	private static class RegularBitvectorOperation_BooleanResult extends RegularBitvectorOperation {

		private final String mName;
		private final Function<BitvectorConstant, Function<BitvectorConstant, Boolean>> mFunction;

		public RegularBitvectorOperation_BooleanResult(final String name,
				final Function<BitvectorConstant, Function<BitvectorConstant, Boolean>> function) {
			super();
			mName = name;
			mFunction = function;
		}

		@Override
		public String getFunctionName() {
			return mName;
		}

		@Override
		public Term simplify_ConstantCase(final Script script, final BigInteger[] indices,
				final BitvectorConstant[] bvs) {
			return script.term(String.valueOf(mFunction.apply(bvs[0]).apply(bvs[1])));
		}
	}

	private static class Bvnot extends BitvectorOperation {
		@Override
		public String getFunctionName() {
			return "bvnot";
		}

		@Override
		public int getNumberOfIndices() {
			return 0;
		}

		@Override
		public int getNumberOfParams() {
			return 1;
		}

		@Override
		public Term simplify_ConstantCase(final Script script, final BigInteger[] indices,
				final BitvectorConstant[] bvs) {
			return constructTerm(script, BitvectorConstant.bvnot(bvs[0]));
		}

	}

	private static class Bvneg extends BitvectorOperation {
		@Override
		public String getFunctionName() {
			return "bvneg";
		}

		@Override
		public int getNumberOfIndices() {
			return 0;
		}

		@Override
		public int getNumberOfParams() {
			return 1;
		}

		@Override
		public Term simplify_ConstantCase(final Script script, final BigInteger[] indices,
				final BitvectorConstant[] bvs) {
			return constructTerm(script, BitvectorConstant.bvneg(bvs[0]));
		}

	}

	private static class Bvand extends RegularBitvectorOperation_BitvectorResult {

		public Bvand() {
			super("bvand", x -> y -> BitvectorConstant.bvand(x, y));
		}

		@Override
		protected Term simplify_NonConstantCase(final Script script, final BigInteger[] indices, final Term[] params,
				final BitvectorConstant[] bvs) {
			for (final BitvectorConstant bvConst : bvs) {
				if (bvConst != null && bvConst.getValue().equals(BigInteger.ZERO)) {
					return constructTerm(script, bvConst);
				}
			}
			return super.simplify_NonConstantCase(script, indices, params, bvs);
		}
	}

}
