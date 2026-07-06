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
import java.util.function.Function;

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
			result = new Bvand().simplifiedResult(script, funcname, indices, params);
			break;
		case bvor:
			result = new NaryBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvor(x, y))
					.simplifiedResult(script, funcname, indices, params);
			break;
		case bvxor:
			result = new NaryBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvxor(x, y))
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
			result = SmtUtils.oldAPITerm(script, funcname, indices, null, params);
			break;
		}
		return result;
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

	private static class NaryBitvectorOperation_BitvectorResult extends BitvectorOperation {

		private final String mName;
		private final Function<BitvectorConstant, Function<BitvectorConstant, BitvectorConstant>> mConstantSimplification;

		public NaryBitvectorOperation_BitvectorResult(final String name,
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
			return true; // AND, OR und XOR are all commutative!
		}

		@Override
		public int getNumberOfIndices() {
			return 0;
		}

		@Override
		public int getNumberOfParams() {
			return -1; // for accepting more than two params
		}

		@Override
		public Term simplify_ConstantCase(final Script script, final BigInteger[] indices,
				final BitvectorConstant[] bvs) {
			// calculate all literals together
			BitvectorConstant result = bvs[0];
			for (int i = 1; i < bvs.length; i++) {
				result = mConstantSimplification.apply(result).apply(bvs[i]);
			}
			return constructTerm(script, result);
		}

		@Override
		protected Term simplify_NonConstantCase(final Script script, final BigInteger[] indices, final Term[] params,
				final BitvectorConstant[] bvs) {

			// 1. Flattening
			final List<Term> flatArgs = new ArrayList<>();
			for (final Term p : params) {
				final ApplicationTerm appTerm = SmtUtils.getFunctionApplication(p, getFunctionName());
				if (appTerm != null) {
					flatArgs.addAll(Arrays.asList(appTerm.getParameters()));
				} else {
					flatArgs.add(p);
				}
			}

			// 2. Split and Sort
			// Constante --> Literal, Variable --> Non-Literal
			final List<BitvectorConstant> constants = new ArrayList<>();
			final List<Term> variables = new ArrayList<>();

			for (final Term t : flatArgs) {
				final BitvectorConstant bc = BitvectorUtils.constructBitvectorConstant(t);
				if (bc != null) {
					constants.add(bc);
				} else {
					variables.add(t);
				}
			}
			final Term[] sortedVariables = CommuhashUtils.sortByHashCode(variables.toArray(new Term[0]));

			// 3. Constant Folding
			BitvectorConstant mergedConstant = null;
			if (!constants.isEmpty()) {
				mergedConstant = constants.get(0);
				for (int i = 1; i < constants.size(); i++) {
					mergedConstant = mConstantSimplification.apply(mergedConstant).apply(constants.get(i));
				}
			}

			// 4. Duplicate Elimination
			// Note: a plain Set is NOT enough here. bvand/bvor are idempotent (X AND X == X), so presence alone
			// would suffice - but bvxor is nilpotent (X XOR X == 0): an even count cancels out, an odd count
			// leaves one copy (e.g. X XOR X XOR X == X). That's a parity check, not a presence check, so
			// removeDuplicates() below counts runs of equal terms (after sorting) and, per getFunctionName(),
			// either keeps one copy (bvand/bvor) or keeps it only if the run length is odd (bvxor). The sort is
			// also needed independently to reach the canonical "Commuhash Normal Form" argument order.
			final List<Term> uniqueVariables = removeDuplicates(sortedVariables, getFunctionName());

			// 5. Absorption & Annihilation
			if (mergedConstant != null) {
				final BigInteger value = mergedConstant.getValue();

				// The bit width is available directly as a BigInteger via getIndex(), no need to go through
				// getStringIndex() and parse it back into an int.
				// The "all ones" value (2^n - 1) does not need to be computed by hand either: BitvectorConstant
				// already provides this via its maxValue(...) factory method, which we reuse here for consistency
				// with the rest of the codebase and to avoid duplicating the 2^n - 1 formula.
				final BigInteger allOnes = BitvectorConstant.maxValue(mergedConstant.getIndex()).getValue();

				if (value.equals(BigInteger.ZERO)) {
					if (getFunctionName().equals("bvand")) {
						// Annihilation: X AND 0 = 0. Ignore rest of formula.
						return constructTerm(script, mergedConstant);
					} else if (getFunctionName().equals("bvor") || getFunctionName().equals("bvxor")) {
						// Absorption: X OR 0 = X, X XOR 0 = X. The 0 drops out.
						mergedConstant = null;
					}
				} else if (value.equals(allOnes)) {
					if (getFunctionName().equals("bvor")) {
						// Annihilation: X OR 1111 = 1111
						return constructTerm(script, mergedConstant);
					} else if (getFunctionName().equals("bvand")) {
						// Absorption: X AND 1111 = X
						mergedConstant = null;
					}
				}
			}

			// 6. final construction
			final List<Term> finalArgs = new ArrayList<>();
			if (mergedConstant != null) {
				finalArgs.add(constructTerm(script, mergedConstant));
			}
			finalArgs.addAll(uniqueVariables);

			// handle edge cases
			if (finalArgs.isEmpty()) {

				// This branch is reachable, not dead code: it is hit whenever every argument cancels out, which
				// can only happen for bvxor (nilpotence, e.g. "x XOR x" with no constant involved at all) since
				// bvand/bvor only ever drop the constant, never a variable. See test bvxorNilpotencePairCancels
				// in BitvectorUtilTest.java for a concrete example that exercises exactly this path.
				// If everything is gone, 0 remains. We get the sort (type) from the very first parameter.
				return BitvectorUtils.constructTerm(script, BigInteger.ZERO, params[0].getSort());
			} else if (finalArgs.size() == 1) {
				// If only one element remains, we don't need an operator anymore (e.g., "AND(V1)" becomes "V1")
				return finalArgs.get(0);
			} else {
				// Use CommuhashUtils.term instead of SmtUtils.oldAPITerm here, not just for style: bvand/bvor/bvxor
				// are registered as commutative in CommuhashUtils.isKnownToBeCommutative, so CommuhashUtils.term
				// re-sorts ALL parameters by hash code before constructing the term. CommuhashUtils.term fixes this by
				// sorting the full parameter list (constant included) right before term construction.
				return CommuhashUtils.term(script, getFunctionName(), SmtUtils.toStringArray(indices), null,
						finalArgs.toArray(new Term[0]));

			}
		}

		private static List<Term> removeDuplicates(final Term[] sortedVariables, final String operatorName) {
			final List<Term> uniqueVariables = new ArrayList<>();

			int i = 0;
			while (i < sortedVariables.length) {
				final Term current = sortedVariables[i];
				int count = 1;

				// count identical neighbors
				while (i + 1 < sortedVariables.length && current.equals(sortedVariables[i + 1])) {
					count++;
					i++;
				}

				if (operatorName.equals("bvxor")) {
					if (count % 2 != 0) {
						// Nilpotenz
						uniqueVariables.add(current);
					}
				} else {
					// Idempotenz
					uniqueVariables.add(current);
				}

				i++;
			}

			return uniqueVariables;
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

	private static class Bvand extends NaryBitvectorOperation_BitvectorResult { // now extends new
																				// NaryBitvectorOperation

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
