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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
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
	 * {@link RelationSymbol#swapParameters()}; the actual term is then built by dispatching back into
	 * {@link #unfTerm}, so the existing bvult/bvule/bvslt/bvsle handling (including constant folding) is reused
	 * as-is instead of being duplicated here.
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

	/**
	 * Simplifies a (possibly n-ary) application of {@code bvand}. Folds constant arguments into a single
	 * {@link BitvectorConstant}, flattens nested {@code bvand} applications, removes duplicate operands (bvand is
	 * idempotent: X bvand X = X), and applies the annihilating ({@code 0}) and identity ({@code 1...1}) constants.
	 *
	 * @param params
	 *            the operands of the {@code bvand} application, not necessarily constant
	 * @return the simplified term, or an unsimplified {@code bvand} application if no simplification was possible
	 */
	static Term simplifyBvand(final Script script, final Term[] params) {
		for (final Term p : params) {
			final BitvectorConstant bv = constructBitvectorConstant(p);
			if (bv != null && bv.getValue().equals(BigInteger.ZERO)) {
				return constructTerm(script, bv); // X bvand 0 = 0
			}
		}

		final List<Term> flatArgs = flatten(params, "bvand");
		final List<BitvectorConstant> literals = new ArrayList<>();
		final List<Term> nonLiterals = new ArrayList<>();
		splitIntoLiteralsAndNonLiterals(flatArgs, literals, nonLiterals);
		final Term[] sortedNonLiterals = CommuhashUtils.sortByHashCode(nonLiterals.toArray(new Term[0]));
		final List<Term> reducedNonLiterals = collectIdempotent(sortedNonLiterals);

		BitvectorConstant mergedConstant = foldLiterals(literals, BitvectorConstant::bvand);
		if (mergedConstant != null) {
			if (mergedConstant.getValue().equals(BigInteger.ZERO)) {
				return constructTerm(script, mergedConstant); // Annihilation
			}
			if (isAllOnes(mergedConstant) && !reducedNonLiterals.isEmpty()) {
				mergedConstant = null; // Identitaet faellt nur weg, wenn noch etwas anderes uebrig ist
			}
		}

		final List<Term> finalArgs = new ArrayList<>();
		if (mergedConstant != null) {
			finalArgs.add(constructTerm(script, mergedConstant));
		}
		finalArgs.addAll(reducedNonLiterals);

		if (finalArgs.size() == 1) {
			return finalArgs.get(0);
		}
		return CommuhashUtils.term(script, "bvand", null, null, finalArgs.toArray(new Term[0]));
	}

	/**
	 * Simplifies a (possibly n-ary) application of {@code bvor}. Same algorithm as {@link #simplifyBvand}, mirrored:
	 * {@code bvor} is idempotent, its annihilator is {@code 1...1} and its identity is {@code 0}.
	 *
	 * @param params
	 *            the operands of the {@code bvor} application, not necessarily constant
	 * @return the simplified term, or an unsimplified {@code bvor} application if no simplification was possible
	 */
	static Term simplifyBvor(final Script script, final Term[] params) {
		final List<Term> flatArgs = flatten(params, "bvor");
		final List<BitvectorConstant> literals = new ArrayList<>();
		final List<Term> nonLiterals = new ArrayList<>();
		splitIntoLiteralsAndNonLiterals(flatArgs, literals, nonLiterals);
		final Term[] sortedNonLiterals = CommuhashUtils.sortByHashCode(nonLiterals.toArray(new Term[0]));
		final List<Term> reducedNonLiterals = collectIdempotent(sortedNonLiterals);

		BitvectorConstant mergedConstant = foldLiterals(literals, BitvectorConstant::bvor);
		if (mergedConstant != null) {
			if (isAllOnes(mergedConstant)) {
				return constructTerm(script, mergedConstant); // Annihilation
			}
			if (mergedConstant.getValue().equals(BigInteger.ZERO) && !reducedNonLiterals.isEmpty()) {
				mergedConstant = null; // Identitaet faellt nur weg, wenn noch etwas anderes uebrig ist
			}
		}

		final List<Term> finalArgs = new ArrayList<>();
		if (mergedConstant != null) {
			finalArgs.add(constructTerm(script, mergedConstant));
		}
		finalArgs.addAll(reducedNonLiterals);

		if (finalArgs.size() == 1) {
			return finalArgs.get(0);
		}
		return CommuhashUtils.term(script, "bvor", null, null, finalArgs.toArray(new Term[0]));
	}

	/**
	 * Simplifies a (possibly n-ary) application of {@code bvxor}. Folds constant arguments, flattens nested
	 * {@code bvxor} applications, and removes operand pairs that cancel out (bvxor is nilpotent: X bvxor X = 0), so an
	 * operand survives only if it occurs an odd number of times. Unlike {@link #simplifyBvand}/{@link #simplifyBvor},
	 * {@code bvxor} has no annihilating constant, only the identity {@code 0}.
	 *
	 * @param params
	 *            the operands of the {@code bvxor} application, not necessarily constant
	 * @return the simplified term, or an unsimplified {@code bvxor} application if no simplification was possible
	 */
	static Term simplifyBvxor(final Script script, final Term[] params) {
		final List<Term> flatArgs = flatten(params, "bvxor");
		final List<BitvectorConstant> literals = new ArrayList<>();
		final List<Term> nonLiterals = new ArrayList<>();
		splitIntoLiteralsAndNonLiterals(flatArgs, literals, nonLiterals);
		final Term[] sortedNonLiterals = CommuhashUtils.sortByHashCode(nonLiterals.toArray(new Term[0]));
		final List<Term> reducedNonLiterals = collectXor(sortedNonLiterals);

		BitvectorConstant mergedConstant = foldLiterals(literals, BitvectorConstant::bvxor);
		if (mergedConstant != null && mergedConstant.getValue().equals(BigInteger.ZERO)
				&& !reducedNonLiterals.isEmpty()) {
			mergedConstant = null; // kein Annihilator bei bvxor, nur Identitaet
		}

		final List<Term> finalArgs = new ArrayList<>();
		if (mergedConstant != null) {
			finalArgs.add(constructTerm(script, mergedConstant));
		}
		finalArgs.addAll(reducedNonLiterals);

		if (finalArgs.isEmpty()) {
			return constructTerm(script, BigInteger.ZERO, params[0].getSort()); // z.B. "x xor x" -> 0
		}
		if (finalArgs.size() == 1) {
			return finalArgs.get(0);
		}
		return CommuhashUtils.term(script, "bvxor", null, null, finalArgs.toArray(new Term[0]));
	}

	/**
	 * Flattens nested applications of {@code funcname} into a single argument list, e.g. for {@code funcname =
	 * "bvand"} the arguments of {@code (bvand a (bvand b c))} become {@code [a, b, c]}. Only one level is unwrapped
	 * per argument on purpose: arguments are built bottom-up and are therefore already flat, so a recursive descent
	 * would be redundant.
	 *
	 * @param params
	 *            the top-level arguments of the application, some of which may themselves be {@code funcname}
	 *            applications
	 * @param funcname
	 *            name of the associative operator being flattened ({@code bvand}, {@code bvor} or {@code bvxor})
	 * @return the flattened argument list
	 */
	private static List<Term> flatten(final Term[] params, final String funcname) {
		final List<Term> flatArgs = new ArrayList<>();
		for (final Term p : params) {
			final ApplicationTerm appTerm = SmtUtils.getFunctionApplication(p, funcname);
			if (appTerm != null) {
				flatArgs.addAll(Arrays.asList(appTerm.getParameters()));
			} else {
				flatArgs.add(p);
			}
		}
		return flatArgs;
	}

	/**
	 * Splits {@code flatArgs} into bitvector literals (collected as {@link BitvectorConstant}s, for folding via
	 * {@link #foldLiterals}) and non-literals (kept as {@link Term}s). Results are written into the two given,
	 * initially empty output lists.
	 *
	 * @param flatArgs
	 *            the (already flattened) arguments to split
	 * @param literals
	 *            output: the arguments that are bitvector literals
	 * @param nonLiterals
	 *            output: the arguments that are not bitvector literals
	 */
	private static void splitIntoLiteralsAndNonLiterals(final List<Term> flatArgs,
			final List<BitvectorConstant> literals, final List<Term> nonLiterals) {
		for (final Term t : flatArgs) {
			final BitvectorConstant bc = constructBitvectorConstant(t);
			if (bc != null) {
				literals.add(bc);
			} else {
				nonLiterals.add(t);
			}
		}
	}

	/**
	 * Folds all literals into a single {@link BitvectorConstant}, applying {@code fold} left to right.
	 *
	 * @param literals
	 *            the literals to fold, in any order
	 * @param fold
	 *            the constant semantics of the operator, e.g. {@code BitvectorConstant::bvand}
	 * @return the folded constant, or {@code null} if {@code literals} is empty
	 */
	private static BitvectorConstant foldLiterals(final List<BitvectorConstant> literals,
			final BinaryOperator<BitvectorConstant> fold) {
		return literals.stream().reduce(fold).orElse(null);
	}

	/**
	 * Collector for the idempotent operators bvand/bvor: since X op X = X every term is kept exactly once. The input
	 * is already sorted, so {@code distinct()} removes duplicates while preserving that order.
	 *
	 * @param sortedNonLiterals
	 *            non-literal operands, sorted into Commuhash normal form
	 * @return the operands with duplicates removed, in the same order
	 */
	private static List<Term> collectIdempotent(final Term[] sortedNonLiterals) {
		return Arrays.stream(sortedNonLiterals).distinct().collect(Collectors.toList());
	}

	/**
	 * Collector for the nilpotent operator bvxor: since X xor X = 0 a term survives only if it occurs an odd number of
	 * times. The input is sorted, so equal terms are adjacent and can be counted in a single pass.
	 *
	 * @param sortedNonLiterals
	 *            non-literal operands, sorted into Commuhash normal form
	 * @return the operands that occur an odd number of times, in the same order
	 */
	private static List<Term> collectXor(final Term[] sortedNonLiterals) {
		final List<Term> result = new ArrayList<>();
		int i = 0;
		while (i < sortedNonLiterals.length) {
			final Term current = sortedNonLiterals[i];
			int count = 1;
			while (i + 1 < sortedNonLiterals.length && current.equals(sortedNonLiterals[i + 1])) {
				count++;
				i++;
			}
			if (count % 2 != 0) {
				result.add(current);
			}
			i++;
		}
		return result;
	}

	/**
	 * @return true iff the given bitvector constant is the all-ones value (2^width - 1), i.e. every bit is set. Kept as
	 *         a small reusable check (used here for absorption/annihilation) instead of recomputing the 2^width - 1
	 *         formula inline.
	 */
	private static boolean isAllOnes(final BitvectorConstant bv) {
		return bv.getValue().equals(BitvectorConstant.maxValue(bv.getIndex()).getValue());
	}
}
