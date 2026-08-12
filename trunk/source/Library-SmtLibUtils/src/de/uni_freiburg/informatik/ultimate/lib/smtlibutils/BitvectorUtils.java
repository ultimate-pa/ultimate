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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant.BvOp;

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
		if (!SmtSortUtils.isBitvecSort(term.getSort())) {
			return null;
		}
		if (term instanceof ApplicationTerm && term.getSort().getIndices().length == 1) {
			final FunctionSymbol symb = ((ApplicationTerm) term).getFunction();
			if (!isBitvectorConstant(symb)) {
				return null;
			}
			assert symb.getName().startsWith("bv");
			final String valueString = symb.getName().substring(2);
			return constructBitvectorConstant(new BigInteger(valueString), term.getSort());
		}
		if (term instanceof ConstantTerm) {
			final BigInteger value = extractValueFromBitvectorConstant((ConstantTerm) term);
			return constructBitvectorConstant(value, term.getSort());
		}
		return null;
	}

	public static BitvectorConstant constructBitvectorConstant(final BigInteger value, final Sort sort) {
		final String index = sort.getIndices()[0];
		return new BitvectorConstant(value, index);
	}

	public static BigInteger extractValueFromBitvectorConstant(final ConstantTerm term) {
		if (!SmtSortUtils.isBitvecSort(term.getSort())) {
			throw new AssertionError("Sort must be bitvector sort, got " + term.getSort());
		}
		final Object value = term.getValue();
		if (value instanceof BigInteger) {
			return (BigInteger) value;
		}
		if (value.toString().startsWith("#x")) {
			return new BigInteger(value.toString().substring(2), 16);
		}
		if (value.toString().startsWith("#b")) {
			return new BigInteger(value.toString().substring(2), 2);
		}
		throw new AssertionError(
				"Value must be stored as BigInterger, hexadecimally endoded string or binarily encoded string");
	}

	/**
	 * @return Term that represents bitvector (value % 2^index)
	 */
	public static Term constructTerm(final Script script, final BigInteger value, final Sort sort) {
		final String index = sort.getIndices()[0];
		return constructTerm(script, new BitvectorConstant(value, index));
	}

	public static Term constructTerm(final Script script, final BitvectorConstant bitvec) {
		final String funcname = "bv" + bitvec.getValue().toString();
		return script.term(funcname, new String[] { bitvec.getStringIndex() }, null);
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

	public static Term unfTerm(final Script script, final String funcname, final BigInteger[] indices,
			final Term... params) {
		final Term result;
		final BvOp bvop = BvOp.valueOf(funcname);
		switch (bvop) {
		case zero_extend:
			result = new Zero_extend().simplifiedResult(script, funcname, indices, params);
			break;
		case sign_extend:
			result = new Sign_extend().simplifiedResult(script, funcname, indices, params);
			break;
		case extract:
			result = new Extract().simplifiedResult(script, funcname, indices, params);
			break;
		case concat:
			result = new Concat().simplifiedResult(script, funcname, indices, params);
			break;
		case bvadd:
			result = SmtUtils.sum(script, funcname, params);
			break;
		case bvsub:
			result = SmtUtils.minus(script, params);
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
		case bvsmod:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvsmod(x, y))
					.simplifiedResult(script, funcname, indices, params);
			break;
		case bvmul:
			result = SmtUtils.mul(script, funcname, params);
			break;
		case bvand:
			result = simplifyBvand(script, params);
			break;
		case bvor:
			result = simplifyBvor(script, params);
			break;
		case bvxor:
			result = simplifyBvxor(script, params);
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
		case bvuge:
			// Mirror to the "less" form instead of folding these separately, e.g. (bvugt a b) -> (bvult b a).
			result = mirrorGreaterOperator(script, funcname, indices, params);
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
		case bvsge:
			// Same mirroring for the signed "greater" operators, e.g. (bvsge a b) -> (bvsle b a).
			result = mirrorGreaterOperator(script, funcname, indices, params);
			break;
		default:
			if (BitvectorUtils.allTermsAreBitvectorConstants(params)) {
				throw new AssertionError("wasted optimization " + funcname);
			}
			result = SmtUtils.oldAPITerm(script, funcname, indices, null, params);
			break;
		}
		return result;
	}

	/**
	 * Rewrites a "greater than" comparison ({@code bvugt}, {@code bvuge}, {@code bvsgt}, {@code bvsge}) into its
	 * mirrored "less than" form by swapping the two operands, e.g. {@code (bvugt a b)} becomes {@code (bvult b a)}.
	 * This keeps only 4 comparison operators in normal form instead of 8. The mirrored operator name comes from
	 * {@link RelationSymbol#swapParameters()}; the actual term is then built by dispatching back into {@link #unfTerm},
	 * so the existing bvult/bvule/bvslt/bvsle handling (including constant folding) is reused as-is instead of being
	 * duplicated here.
	 *
	 * @param params
	 *            the two operands of the "greater than" comparison, in their original (unswapped) order
	 * @return the term constructed for the mirrored "less than" comparison
	 */
	private static Term mirrorGreaterOperator(final Script script, final String funcname, final BigInteger[] indices,
			final Term... params) {
		final String mirroredFuncname = RelationSymbol.convert(funcname).swapParameters().toString();
		return unfTerm(script, mirroredFuncname, indices, params[1], params[0]);
	}

	private static abstract class BitvectorOperation {

		public final Term simplifiedResult(final Script script, final String funcname, final BigInteger[] indices,
				final Term... params) {
			if (!getFunctionName().equals(funcname)) {
				throw new AssertionError("Wrong function name: " + funcname);
			}
			assert (getNumberOfIndices() == 0 && indices == null || getNumberOfIndices() == indices.length)
					: "Wrong number of indices:" + Arrays.toString(indices);
			// accept more than two params
			if (getNumberOfParams() != -1 && getNumberOfParams() != params.length) {
				throw new AssertionError(String.format("%s: params expected %s, params provided %s", funcname,
						getNumberOfParams(), params.length));
			}
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
			final Term[] newParams;
			if (isCommutative()) {
				newParams = CommuhashUtils.sortByHashCode(params);
			} else {
				newParams = params;
			}
			return SmtUtils.oldAPITerm(script, getFunctionName(), indices, null, newParams);
		}

		public abstract String getFunctionName();

		public abstract boolean isCommutative();

		public abstract int getNumberOfIndices();

		public abstract int getNumberOfParams();

		public abstract Term simplify_ConstantCase(Script script, BigInteger[] indices, BitvectorConstant[] bvs);
	}

	private static class Concat extends BitvectorOperation {

		@Override
		public String getFunctionName() {
			return "concat";
		}

		@Override
		public boolean isCommutative() {
			return false;
		}

		@Override
		public int getNumberOfIndices() {
			return 0;
		}

		@Override
		public int getNumberOfParams() {
			return 2;
		}

		@Override
		public Term simplify_ConstantCase(final Script script, final BigInteger[] indices,
				final BitvectorConstant[] bvs) {
			final BitvectorConstant bv = BitvectorConstant.concat(bvs[0], bvs[1]);
			return constructTerm(script, bv);
		}

	}

	private static class Extract extends BitvectorOperation {

		@Override
		public String getFunctionName() {
			return "extract";
		}

		@Override
		public boolean isCommutative() {
			return false;
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

		/**
		 * Extract-over-extend simplification: sign_extend/zero_extend only add bits above the original value, so
		 * extracting bits [hi:0] where hi falls anywhere from the original width up to (but not including) the full
		 * extended width always gives back a smaller extend of the original value, e.g.
		 * {@code (extract 2 0 (sign_extend 2 x))} -> {@code (sign_extend 1 x)} for a 3-bit x, and the special case
		 * {@code (extract 1 0 (sign_extend 2 x))} -> {@code x} where no padding bits survive at all. Extracting the
		 * full extended width, or reaching outside it, is out of scope for this rule.
		 */
		@Override
		protected Term simplify_NonConstantCase(final Script script, final BigInteger[] indices, final Term[] params,
				final BitvectorConstant[] bvs) {
			final int hi = indices[0].intValueExact();
			final int lo = indices[1].intValueExact();
			if (lo == 0) {
				String extendFuncName = "sign_extend";
				ApplicationTerm extendApp = SmtUtils.getFunctionApplication(params[0], extendFuncName);
				if (extendApp == null) {
					extendFuncName = "zero_extend";
					extendApp = SmtUtils.getFunctionApplication(params[0], extendFuncName);
				}
				if (extendApp != null) {
					final Term innerValue = extendApp.getParameters()[0];
					final int innerWidth = Integer.parseInt(innerValue.getSort().getIndices()[0]);
					final int extendedWidth = Integer.parseInt(extendApp.getSort().getIndices()[0]);
					if (hi >= innerWidth - 1 && hi < extendedWidth - 1) {
						final int reducedExtendAmount = hi - (innerWidth - 1);
						if (reducedExtendAmount == 0) {
							return innerValue; // extract exactly undoes the extend
						}
						// fewer padding bits survive than before - shrink the extend instead of dropping it
						return unfTerm(script, extendFuncName,
								new BigInteger[] { BigInteger.valueOf(reducedExtendAmount) }, innerValue);
					}
				}
			}
			return super.simplify_NonConstantCase(script, indices, params, bvs);
		}

	}

	private static class Sign_extend extends BitvectorOperation {

		@Override
		public String getFunctionName() {
			return "sign_extend";
		}

		@Override
		public boolean isCommutative() {
			return false;
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
			final BitvectorConstant bv = BitvectorConstant.sign_extend(bvs[0], indices[0]);
			return constructTerm(script, bv);
		}

	}

	private static class Zero_extend extends BitvectorOperation {

		@Override
		public String getFunctionName() {
			return "zero_extend";
		}

		@Override
		public boolean isCommutative() {
			return false;
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
			mName = name;
			mConstantSimplification = function;
		}

		@Override
		public String getFunctionName() {
			return mName;
		}

		@Override
		public boolean isCommutative() {
			final BvOp bvop = BvOp.valueOf(getFunctionName());
			switch (bvop) {
			case bvadd:
			case bvand:
			case bvmul:
			case bvor:
			case bvxor:
				return true;
			case bvashr:
			case bvlshr:
			case bvsdiv:
			case bvshl:
			case bvsmod:
			case bvsrem:
			case bvurem:
			case bvsub:
			case bvudiv:
				return false;
			case bvneg:
			case bvnot:
			case bvsge:
			case bvsgt:
			case bvsle:
			case bvslt:
			case bvuge:
			case bvugt:
			case bvule:
			case bvult:
			case concat:
			case extract:
			case sign_extend:
			case zero_extend:
				throw new AssertionError("Not a regular bitvector operator with bitvector result: " + bvop);
			default:
				throw new UnsupportedOperationException("Unknown bitvector operator: " + bvop);
			}
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
			mName = name;
			mFunction = function;
		}

		@Override
		public String getFunctionName() {
			return mName;
		}

		@Override
		public boolean isCommutative() {
			return false;
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
		public boolean isCommutative() {
			return false;
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
		public boolean isCommutative() {
			return false;
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

	static Term simplifyBvand(final Script script, final Term[] params) {
		return bitwiseOperationHelper(script, params, SMTLIBConstants.BVAND);
	}

	static Term simplifyBvor(final Script script, final Term[] params) {
		return bitwiseOperationHelper(script, params, SMTLIBConstants.BVOR);
	}

	static Term simplifyBvxor(final Script script, final Term[] params) {
		return bitwiseOperationHelper(script, params, SMTLIBConstants.BVXOR);
	}

	/**
	 * @return true iff the given bitvector constant is the all-ones value (2^width - 1), i.e. every bit is set. Kept as
	 *         a small reusable check (used here for absorption/annihilation) instead of recomputing the 2^width - 1
	 *         formula inline.
	 */
	private static boolean isAllOnes(final BitvectorConstant bv) {
		return bv.getValue().equals(BitvectorConstant.maxValue(bv.getIndex()).getValue());
	}

	/**
	 * Simplifies an n-ary bitwise application: flattens nested same-operator applications, folds all literal operands
	 * into one constant, deduplicates non-literal operands, applies absorption/annihilation, and assembles the final
	 * term - all in one pass over a single Set. Flattening happens inline (no intermediate list) and annihilation is
	 * checked directly inside the loop, since it only depends on the folded constant itself; absorption (dropping an
	 * identity constant) has to wait until the loop finishes, since it depends on whether any non-literal survived.
	 *
	 * @param funcname
	 *            one of {@link #BVAND}, {@link #BVOR}, {@link #BVXOR}
	 * @param params
	 *            the top-level arguments of the application, not necessarily flattened or literal
	 * @return the simplified term
	 */
	private static Term bitwiseOperationHelper(final Script script, final Term[] params, final String funcname) {
		final BinaryOperator<BitvectorConstant> fold;
		final Predicate<BitvectorConstant> isAnnihilating;
		final Predicate<BitvectorConstant> isIdentity;
		switch (funcname) {
		case SMTLIBConstants.BVAND:
			fold = BitvectorConstant::bvand;
			isAnnihilating = bc -> bc.getValue().equals(BigInteger.ZERO);
			isIdentity = BitvectorUtils::isAllOnes;
			break;
		case SMTLIBConstants.BVOR:
			fold = BitvectorConstant::bvor;
			isAnnihilating = BitvectorUtils::isAllOnes;
			isIdentity = bc -> bc.getValue().equals(BigInteger.ZERO);
			break;
		case SMTLIBConstants.BVXOR:
			fold = BitvectorConstant::bvxor;
			isAnnihilating = bc -> false; // bvxor has no annihilating constant, only an identity (0)
			isIdentity = bc -> bc.getValue().equals(BigInteger.ZERO);
			break;
		default:
			throw new AssertionError("unsupported operator for bitwiseOperationHelper: " + funcname);
		}
		final boolean isXor = funcname.equals(SMTLIBConstants.BVXOR);

		final Set<Term> result = new HashSet<>();
		BitvectorConstant mergedConstant = null;
		for (final Term p : params) {
			// Unwrap one level of nested same-operator application, or process p itself. Arguments are built
			// bottom-up and are therefore already flat, so a recursive descent would be redundant.
			final ApplicationTerm appTerm = SmtUtils.getFunctionApplication(p, funcname);
			final Term[] toProcess = appTerm != null ? appTerm.getParameters() : new Term[] { p };
			for (final Term t : toProcess) {
				final BitvectorConstant bc = constructBitvectorConstant(t);
				if (bc != null) {
					mergedConstant = (mergedConstant == null) ? bc : fold.apply(mergedConstant, bc);
					if (isAnnihilating.test(mergedConstant)) {
						return constructTerm(script, mergedConstant); // rest of params cannot change this anymore
					}
				} else {
					final boolean isNewTerm = result.add(t);
					if (!isNewTerm && isXor) {
						result.remove(t); // second (or 4th, ...) occurrence cancels: X xor X = 0
					}
				}
			}
		}

		if (mergedConstant != null && isIdentity.test(mergedConstant) && !result.isEmpty()) {
			mergedConstant = null; // identity drops only if something else remains
		}

		if (mergedConstant != null) {
			result.add(constructTerm(script, mergedConstant)); // surviving literal joins the same set
		}

		if (result.isEmpty()) {
			return constructTerm(script, BigInteger.ZERO, params[0].getSort()); // e.g. "x xor x" -> 0
		}
		if (result.size() == 1) {
			return result.iterator().next();
		}
		return CommuhashUtils.term(script, funcname, null, null, result.toArray(new Term[0]));
	}
}
