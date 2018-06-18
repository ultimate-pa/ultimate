/*
 * Copyright (C) 2009-2014 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.logic;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.util.HashUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnifyHash;

/**
 * The theory is not intended for public use. Please stick to the {@link Script} interface and use the functions in
 * {@link Util} to simplify logical formulas.
 *
 * The theory is a container for the function symbols, sort symbols and a unifier for all terms created by this theory.
 * Each sort belongs to one theory and since every function symbol and every term has a sort, they also belong to one
 * theory.
 *
 * The theory also defines all predefined function symbols required by the logic that was set with setLogic(). It allows
 * creating new function and sort symbols.
 *
 * @author Jochen Hoenicke
 */
public class Theory {

	/**
	 * Helper class to set up symbols specific to a solver.
	 *
	 * @author Juergen Christ
	 */
	public static abstract class SolverSetup {
		/**
		 * Set up symbols needed by this solver. These symbols might depend upon the logic, e.g., the diff-symbol needed
		 * for quantifier-free array interpolation.
		 *
		 * @param theory
		 *            The theory to be used by the solver.
		 * @param logic
		 *            The logic set for this theory (@see {@link Theory#getLogic()}).
		 */
		public abstract void setLogic(Theory theory, Logics logic);

		/// *** Delegators ***
		protected final static void declareInternalSort(final Theory theory, final String name, final int cardinality,
				final int flags) {
			theory.declareInternalSort(name, cardinality, flags);
		}

		protected final static void declareInternalFunction(final Theory theory, final String name,
				final Sort[] paramSorts, final Sort resultSort, final int flags) {
			theory.declareInternalFunction(name, paramSorts, resultSort, flags);
		}

		protected final static void declareInternalFunction(final Theory theory, final String name,
				final Sort[] paramTypes, final TermVariable[] defVars, final Term definition, final int flags) {
			theory.declareInternalFunction(name, paramTypes, defVars, definition, flags);
		}

		protected final static void declareInternalPolymorphicFunction(final Theory theory, final String name,
				final Sort[] sortParams, final Sort[] paramTypes, final Sort resultType, final int flags) {
			theory.declareInternalPolymorphicFunction(name, sortParams, paramTypes, resultType, flags);
		}

		protected final static void defineFunction(final Theory theory, final FunctionSymbolFactory factory) {
			theory.defineFunction(factory);
		}
	}

	private SolverSetup mSolverSetup;
	private Logics mLogic;
	private Sort mNumericSort, mRealSort, mStringSort, mBooleanSort;
	private SortSymbol mBitVecSort, mFloatingPointSort;
	private Sort mRoundingModeSort;
	private final HashMap<String, FunctionSymbolFactory> mFunFactory = new HashMap<>();
	private final UnifyHash<FunctionSymbol> mModelValueCache = new UnifyHash<>();

	private final ScopedHashMap<String, SortSymbol> mDeclaredSorts = new ScopedHashMap<>();
	private final ScopedHashMap<String, FunctionSymbol> mDeclaredFuns = new ScopedHashMap<>();

	private final UnifyHash<QuantifiedFormula> mQfCache = new UnifyHash<>();
	private final UnifyHash<LetTerm> mLetCache = new UnifyHash<>();
	private final UnifyHash<Term> mTermCache = new UnifyHash<>();
	private final UnifyHash<TermVariable> mTvUnify = new UnifyHash<>();
	/**
	 * Factory for to_real wrapper function symbol, if IRA logic is used.
	 */
	private IRAWrapperFactory mIRAWrappers;
	/**
	 * Cache for bitvector constant function symbols (_ bv123 456).
	 */
	private UnifyHash<FunctionSymbol> mBitVecConstCache;

	public final ApplicationTerm mTrue, mFalse;
	public final FunctionSymbol mAnd, mOr, mNot, mImplies, mXor;
	public final PolymorphicFunctionSymbol mEquals, mDistinct;

	final static Sort[] EMPTY_SORT_ARRAY = Script.EMPTY_SORT_ARRAY;
	final static TermVariable[] EMPTY_TERM_VARIABLE_ARRAY = {};
	final static Term[] EMPTY_TERM_ARRAY = Script.EMPTY_TERM_ARRAY;
	/**
	 * Pattern for model value variables '{@literal @}digits'.
	 */
	private final static String MODEL_VALUE_PATTERN = "@\\d+";
	private final static String BITVEC_CONST_PATTERN = "bv\\d+";

	private int mTvarCtr = 0;

	private int mSkolemCounter = 0;

	private boolean mGlobalDecls;

	public Theory() {
		mTrue = mFalse = null;
		mAnd = mOr = mNot = mImplies = mXor = null;
		mEquals = mDistinct = null;
	}

	public Theory(final Logics logic) {
		this(logic, null);
	}

	/**
	 * Create the term factory. The solver setup should be used to create internal function symbols, e.g., to represent
	 * proof objects.
	 *
	 * @param logic
	 *            The logic to use.
	 * @param solverSetup
	 *            The solver-specific setup delegate.
	 */
	public Theory(final Logics logic, final SolverSetup solverSetup) {
		mSolverSetup = solverSetup;
		final Sort[] noarg = new Sort[0];
		mBooleanSort = declareInternalSort("Bool", 0, 0).getSort(null, noarg);
		final Sort[] generic1 = createSortVariables("A");
		final Sort[] bool1 = new Sort[] { mBooleanSort };
		final Sort[] bool2 = new Sort[] { mBooleanSort, mBooleanSort };
		final Sort[] generic2 = new Sort[] { generic1[0], generic1[0] };
		final int leftassoc = FunctionSymbol.LEFTASSOC;
		mNot = declareInternalFunction("not", bool1, mBooleanSort, 0);
		mAnd = declareInternalFunction("and", bool2, mBooleanSort, leftassoc);
		mOr = declareInternalFunction("or", bool2, mBooleanSort, leftassoc);
		mImplies = declareInternalFunction("=>", bool2, mBooleanSort, FunctionSymbol.RIGHTASSOC);
		mEquals = declareInternalPolymorphicFunction("=", generic1, generic2, mBooleanSort, FunctionSymbol.CHAINABLE);
		mDistinct = declareInternalPolymorphicFunction("distinct", generic1, generic2, mBooleanSort,
				FunctionSymbol.PAIRWISE);
		mXor = declareInternalFunction("xor", bool2, mBooleanSort, leftassoc);
		declareInternalPolymorphicFunction("ite", generic1,
				new Sort[] { mBooleanSort, generic1[0], generic1[0] }, generic1[0], 0);
		mTrue = term(declareInternalFunction("true", noarg, mBooleanSort, 0));
		mFalse = term(declareInternalFunction("false", noarg, mBooleanSort, 0));
		// Finally, declare logic specific functions
		setLogic(logic);
	}

	/******************** LOGICAL OPERATORS *******************************/

	private Term simplifyAndOr(final FunctionSymbol connector, final Term... subforms) {
		final Term neutral = (connector == mAnd ? mTrue : mFalse);
		final LinkedHashSet<Term> formulas = new LinkedHashSet<>();

		for (final Term f : subforms) {
			if (f == mTrue || f == mFalse) {
				if (f == neutral) {
					continue;
				}
				return f;
			}

			/* Normalize nested and/ors */
			if (f instanceof ApplicationTerm && ((ApplicationTerm) f).getFunction() == connector) {
				for (final Term subf : ((ApplicationTerm) f).getParameters()) {
					formulas.add(subf);
				}
			} else {
				formulas.add(f);
			}
		}
		if (formulas.size() <= 1) { // NOPMD
			if (formulas.isEmpty()) {
				return neutral;
			}
			return formulas.iterator().next();
		}
		final Term[] arrforms = formulas.toArray(new Term[formulas.size()]);
		return term(connector, arrforms);
	}

	public Term not(final Term f) {
		if (f == mTrue) {
			return mFalse;
		}
		if (f == mFalse) {
			return mTrue;
		}
		if (f instanceof ApplicationTerm && ((ApplicationTerm) f).getFunction() == mNot) {
			return ((ApplicationTerm) f).getParameters()[0];
		}
		return term(mNot, f);
	}

	public Term and(final Term... subforms) {
		return simplifyAndOr(mAnd, subforms);
	}

	public Term or(final Term... subforms) {
		return simplifyAndOr(mOr, subforms);
	}

	public Term implies(final Term f, final Term g) {
		if (g == mTrue || f == mTrue) {
			return g;
		}
		if (f == mFalse) {
			return mTrue;
		}
		if (g == mFalse) {
			return not(f);
		}
		if (f == g) {
			return mTrue;
		}
		return term(mImplies, f, g);
	}

	public Term xor(final Term f, final Term g) {
		if (f == mTrue) {
			return not(g);
		}
		if (g == mTrue) {
			return not(f);
		}
		if (f == mFalse) {
			return g;
		}
		if (g == mFalse) {
			return f;
		}
		if (f == g) {
			return mFalse;
		}
		return term(mXor, f, g);
	}

	public Term ifthenelse(final Term c, final Term t, final Term e) {
		if (c == mTrue) {
			return t;
		}
		if (c == mFalse) {
			return e;
		}
		if (t == e) {
			return t;
		}
		if (t == mTrue && e == mFalse) {
			return c;
		}
		if (t == mFalse && e == mTrue) {
			return not(c);
		}
		if (t == mTrue) {
			return term(mOr, c, e);
		}
		if (t == mFalse) {
			return term(mAnd, term(mNot, c), e);
		}
		if (e == mTrue) {
			return term(mImplies, c, t);
		}
		if (e == mFalse) {
			return term(mAnd, c, t);
		}
		return term("ite", c, t, e);
	}

	private Term quantify(final int quant, final TermVariable[] vars, final Term f) {
		if (f == mTrue || f == mFalse) {
			return f;
		}
		final int hash = QuantifiedFormula.hashQuantifier(quant, vars, f);
		for (final QuantifiedFormula qf : mQfCache.iterateHashCode(hash)) {
			if (qf.getQuantifier() == quant && qf.getSubformula() == f && Arrays.equals(vars, qf.getVariables())) {
				return qf;
			}
		}
		final QuantifiedFormula qf = new QuantifiedFormula(quant, vars, f, hash);
		mQfCache.put(hash, qf);
		return qf;
	}

	public Term exists(final TermVariable[] vars, final Term f) {
		return quantify(QuantifiedFormula.EXISTS, vars, f);
	}

	public Term forall(final TermVariable[] vars, final Term f) {
		return quantify(QuantifiedFormula.FORALL, vars, f);
	}

	public Term let(final TermVariable[] vars, final Term[] values, final Term subform) {
		assert (vars.length == values.length);
		if (vars.length == 0) {
			return subform;
		}
		final int hash = LetTerm.hashLet(vars, values, subform);
		for (final LetTerm lt : mLetCache.iterateHashCode(hash)) {
			if (lt.getSubTerm() == subform && Arrays.equals(lt.getVariables(), vars)
					&& Arrays.equals(lt.getValues(), values)) {
				return lt;
			}
		}
		final LetTerm lf = new LetTerm(vars, values, subform, hash);
		mLetCache.put(hash, lf);
		return lf;
	}

	public Term let(final TermVariable var, final Term value, final Term subform) {
		return let(new TermVariable[] { var }, new Term[] { value }, subform);
	}

	public Term distinct(final Term... terms) {
		if (terms.length < 2) {
			return null;
		}
		if (terms.length == 2) {
			if (terms[0] == terms[1]) {
				return mFalse;
			}
			if (terms[0].getSort() == mBooleanSort) {
				if (terms[0] == mFalse) {
					return terms[1];
				}
				if (terms[1] == mFalse) {
					return terms[0];
				}
				if (terms[0] == mTrue) {
					return not(terms[1]);
				}
				if (terms[1] == mTrue) {
					return not(terms[0]);
				}
			}
			return term(mDistinct, terms);
		}
		final HashSet<Term> params = new HashSet<>(Arrays.asList(terms));
		if (params.size() != terms.length) {
			// We had something like (distinct ... a ... a ...)
			return mFalse;
		}
		return term(mDistinct, terms);
	}

	public Term equals(final Term... terms) {
		if (terms.length < 2) {
			return null;
		}
		if (terms.length == 2) {
			if (terms[0] == terms[1]) {
				return mTrue;
			}
			if (terms[0].getSort() == mBooleanSort) {
				if (terms[0] == mTrue) {
					return terms[1];
				}
				if (terms[1] == mTrue) {
					return terms[0];
				}
				if (terms[0] == mFalse) {
					return not(terms[1]);
				}
				if (terms[1] == mFalse) {
					return not(terms[0]);
				}
			}
			return term(mEquals, terms);
		}
		final HashSet<Term> params = new HashSet<>(Arrays.asList(terms));
		if (params.size() == 1) {
			// We had (= a a ... a)
			return mTrue;
		}
		return term(mEquals, terms);
	}

	/******************** CONSTANTS *************************************/

	public Term constant(final Object value, final Sort sort) {
		if (value instanceof Rational) {
			if (!sort.isNumericSort()) {
				throw new SMTLIBException("Not a numeric sort");
			}
			final Rational v = (Rational) value;
			if (!v.isRational()) {
				throw new SMTLIBException("Infinite/NaN value");
			}
			if (sort.getName().equals("Int") && !v.isIntegral()) {
				throw new SMTLIBException("Non-integral value with integer sort");
			}
		}
		final int hash = ConstantTerm.hashConstant(value, sort);
		for (final Term t : mTermCache.iterateHashCode(hash)) {
			if (t instanceof ConstantTerm) {
				final ConstantTerm nt = (ConstantTerm) t;
				if (nt.getSort() == sort && value.equals(nt.getValue())) {
					return nt;
				}
			}
		}
		final ConstantTerm nt = new ConstantTerm(value, sort, hash);
		mTermCache.put(hash, nt);
		return nt;
	}

	public Term numeral(final BigInteger num) {
		Term result = constant(num.abs(), mNumericSort);
		if (num.signum() < 0) {
			final FunctionSymbol neg = getFunction("-", mNumericSort);
			result = term(neg, result);
		}
		return result;
	}

	public Term numeral(final String num) {
		return numeral(new BigInteger(num));
	}

	public Term decimal(BigDecimal value) {
		// Fix for 1 vs 1.0: Normalize to .0 for constants.
		if (value.scale() == 0) {
			value = value.setScale(1);
		}
		Term result = constant(value.abs(), mRealSort);
		if (value.signum() < 0) {
			final FunctionSymbol neg = getFunction("-", mRealSort);
			result = term(neg, result);
		}
		return result;
	}

	public Term decimal(final String value) {
		return decimal(new BigDecimal(value));
	}

	/**
	 * Convert a rational constant to a term of the correct sort. The constant must be integral if the sort is integer.
	 *
	 * @param c
	 *            the constant to convert.
	 * @param sort
	 *            the sort; either Real or Int.
	 * @return an smt term representing constant c.
	 */
	public Term rational(final Rational c, final Sort sort) {
		// This must not be an infinite or a NAN.
		assert c.denominator().signum() == 1;
		if (sort == mRealSort) {
			return rational(c.numerator(), c.denominator());
		}
		assert c.isIntegral();
		return numeral(c.numerator());
	}

	public Term binary(final String value) {
		assert value.startsWith("#b");
		if (mBitVecSort == null) {
			return null;
		}
		final BigInteger bsize = BigInteger.valueOf(value.length() - 2);
		final Sort sort = mBitVecSort.getSort(new BigInteger[] { bsize }, new Sort[0]);
		return new ConstantTerm(value, sort, ConstantTerm.hashConstant(value, sort));
	}

	public Term hexadecimal(final String value) {
		assert value.startsWith("#x");
		if (mBitVecSort == null) {
			return null;
		}
		final BigInteger bsize = BigInteger.valueOf(4 * (value.length() - 2));// NOCHECKSTYLE
		final Sort sort = mBitVecSort.getSort(new BigInteger[] { bsize }, new Sort[0]);
		return new ConstantTerm(value, sort, ConstantTerm.hashConstant(value, sort));
	}

	public Term rational(BigInteger num, BigInteger denom) {
		BigInteger gcd = num.gcd(denom);
		if (denom.signum() * gcd.signum() < 0) {
			gcd = gcd.negate();
		}
		num = num.divide(gcd);
		denom = denom.divide(gcd);

		if (denom.equals(BigInteger.ONE)) {
			return decimal(new BigDecimal(num));
		}
		final FunctionSymbol div = getFunction("/", mRealSort, mRealSort);
		return term(div, decimal(new BigDecimal(num)), decimal(new BigDecimal(denom)));
	}

	public Term modelRational(final Rational rat, final Sort sort) {
		final BigInteger num = rat.numerator();
		final BigInteger denom = rat.denominator();

		if (sort == mRealSort) {
			if (mLogic.isIRA()) {
				final FunctionSymbol div = getFunction("/", mRealSort, mRealSort);
				final FunctionSymbol toreal = getFunction("to_real", mNumericSort);
				Term numeralTerm = term(toreal, numeral(num.abs()));
				if (num.signum() < 0) {
					numeralTerm = term("-", numeralTerm);
				}
				return term(div, numeralTerm, term(toreal, numeral(denom)));
			} else {
				if (denom.equals(BigInteger.ONE)) {
					return decimal(new BigDecimal(num));
				}
				final FunctionSymbol div = getFunction("/", mNumericSort, mNumericSort);
				return term(div, numeral(num), numeral(denom));
			}
		} else {
			assert denom.equals(BigInteger.ONE);
			return numeral(rat.numerator());
		}
	}

	public Term string(final String value) {
		return constant(new QuotedObject(value), mStringSort);
	}

	/******************** LOGICS AND THEORIES ********************************/
	public Logics getLogic() {
		return mLogic;
	}

	public FunctionSymbol declareInternalFunction(final String name, final Sort[] paramTypes, final Sort resultType,
			final int flags) {
		return defineFunction(name, paramTypes, resultType, null, null, flags | FunctionSymbol.INTERNAL);
	}

	public FunctionSymbol declareInternalFunction(final String name, final Sort[] paramTypes, final TermVariable[] defVars,
			final Term definition, final int flags) {
		return defineFunction(name, paramTypes, definition.getSort(), defVars, definition,
				flags | FunctionSymbol.INTERNAL);
	}

	public PolymorphicFunctionSymbol declareInternalPolymorphicFunction(final String name, final Sort[] sortParams,
			final Sort[] paramTypes, final Sort resultType, final int flags) {
		assert !mFunFactory.containsKey(name);
		final PolymorphicFunctionSymbol f = new PolymorphicFunctionSymbol(name, sortParams, paramTypes, resultType,
				flags | FunctionSymbol.INTERNAL);
		defineFunction(f);
		return f;
	}

	class MinusFunctionFactory extends FunctionSymbolFactory {
		Sort mSort1, mSort2;

		public MinusFunctionFactory(final Sort sort1, final Sort sort2) {
			super("-");
			mSort1 = sort1;
			mSort2 = sort2;
		}

		@Override
		public int getFlags(final BigInteger[] indices, final Sort[] paramSorts, final Sort resultSort) {
			return paramSorts.length == 1 ? FunctionSymbol.INTERNAL
					: FunctionSymbol.LEFTASSOC | FunctionSymbol.INTERNAL;
		}

		@Override
		public Sort getResultSort(final BigInteger[] indices, final Sort[] paramSorts, final Sort resultSort) {
			if (indices != null || paramSorts.length == 0 || paramSorts.length > 2 || resultSort != null
					|| (paramSorts[0] != mSort1 && paramSorts[0] != mSort2)) {
				return null;
			}

			if (paramSorts.length == 2 && paramSorts[0] != paramSorts[1]) {
				return null;
			}

			return paramSorts[0];
		}
	}

	class DivisibleFunctionFactory extends FunctionSymbolFactory {
		public DivisibleFunctionFactory() {
			super("divisible");
		}

		@Override
		public Sort getResultSort(final BigInteger[] indices, final Sort[] paramSorts, final Sort resultSort) {
			return indices != null && indices.length == 1 && indices[0].signum() > 0 && paramSorts.length == 1
					&& paramSorts[0] == mNumericSort && resultSort == null ? mBooleanSort : null;
		}
	}

	private void createNumericOperators(final Sort sort, final boolean isRational) {
		final Sort[] sort1 = new Sort[] { sort };
		final Sort[] sort2 = new Sort[] { sort, sort };
		declareInternalFunction("+", sort2, sort, FunctionSymbol.LEFTASSOC);
		defineFunction(new MinusFunctionFactory(sort, sort));
		declareInternalFunction("*", sort2, sort, FunctionSymbol.LEFTASSOC);
		if (isRational) {
			declareInternalFunction("/", sort2, sort, FunctionSymbol.LEFTASSOC);
		} else {
			declareInternalFunction("div", sort2, sort, FunctionSymbol.LEFTASSOC);
			declareInternalFunction("mod", sort2, sort, 0);
			defineFunction(new DivisibleFunctionFactory());
		}
		final Sort sBool = mBooleanSort;
		declareInternalFunction(">", sort2, sBool, FunctionSymbol.CHAINABLE);
		declareInternalFunction(">=", sort2, sBool, FunctionSymbol.CHAINABLE);
		declareInternalFunction("<", sort2, sBool, FunctionSymbol.CHAINABLE);
		declareInternalFunction("<=", sort2, sBool, FunctionSymbol.CHAINABLE);

		final TermVariable x = createTermVariable("x1", sort);
		final Term zero = isRational ? decimal("0.0") : numeral("0");
		final Term absx = term("ite", term(">=", x, zero), x, term("-", x));
		declareInternalFunction("abs", sort1, new TermVariable[] { x }, absx, 0);
	}

	private void createIRAOperators() {
		mIRAWrappers = new IRAWrapperFactory();
		class BinArithFactory extends FunctionSymbolFactory {
			Sort mReturnSort;
			int mFlags;

			BinArithFactory(final String name, final Sort returnSort, final int flags) {
				super(name);
				mReturnSort = returnSort;
				mFlags = flags | FunctionSymbol.INTERNAL;
			}

			@Override
			public int getFlags(final BigInteger[] indices, final Sort[] paramSorts, final Sort resultSort) {
				return mFlags;
			}

			@Override
			public Sort getResultSort(final BigInteger[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices == null && paramSorts.length == 2 && paramSorts[0] == paramSorts[1]
						&& (paramSorts[0] == mNumericSort || paramSorts[0] == mRealSort) && resultSort == null) {
					return mReturnSort == null ? paramSorts[0] : mReturnSort;
				}
				return null;
			}
		}

		defineFunction(new BinArithFactory("+", null, FunctionSymbol.LEFTASSOC));
		defineFunction(new MinusFunctionFactory(mNumericSort, mRealSort));
		defineFunction(new BinArithFactory("*", null, FunctionSymbol.LEFTASSOC));
		defineFunction(new BinArithFactory(">", mBooleanSort, FunctionSymbol.CHAINABLE));
		defineFunction(new BinArithFactory(">=", mBooleanSort, FunctionSymbol.CHAINABLE));
		defineFunction(new BinArithFactory("<", mBooleanSort, FunctionSymbol.CHAINABLE));
		defineFunction(new BinArithFactory("<=", mBooleanSort, FunctionSymbol.CHAINABLE));

		final Sort[] int1 = new Sort[] { mNumericSort };
		final Sort[] int2 = new Sort[] { mNumericSort, mNumericSort };
		final Sort[] real1 = new Sort[] { mRealSort };
		final Sort[] real2 = new Sort[] { mRealSort, mRealSort };
		declareInternalFunction("/", real2, mRealSort, FunctionSymbol.LEFTASSOC);
		declareInternalFunction("div", int2, mNumericSort, FunctionSymbol.LEFTASSOC);
		defineFunction(new DivisibleFunctionFactory());
		declareInternalFunction("to_real", int1, mRealSort, 0);
		declareInternalFunction("to_int", real1, mNumericSort, 0);

		declareInternalFunction("mod", int2, mNumericSort, 0);
		final TermVariable xr = createTermVariable("x1", mRealSort);
		// isint x: (= x (to_real (to_int x)))
		final Term isintx = term("=", xr, term("to_real", term("to_int", xr)));
		declareInternalFunction("is_int", real1, new TermVariable[] { xr }, isintx, 0);

		defineFunction(new FunctionSymbolFactory("abs") {
			@Override
			public Term getDefinition(final TermVariable[] tvs, final Sort resultSort) {
				final Term zero = (resultSort == mNumericSort) ? numeral("0") : decimal("0.0");
				// abs x: (ite (>= x 0) x (- x))
				return term("ite", term(">=", tvs[0], zero), tvs[0], term("-", tvs[0]));
			}

			@Override
			public Sort getResultSort(final BigInteger[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices == null && paramSorts.length == 1
						&& (paramSorts[0] == mNumericSort || paramSorts[0] == mRealSort) && resultSort == null) {
					return paramSorts[0];
				}
				return null;
			}
		});

	}

	private void createArrayOperators() {
		final Sort[] generic2 = createSortVariables("X", "Y");
		final SortSymbol arraySort = declareInternalSort("Array", 2, SortSymbol.ARRAY);

		// (Array X Y)
		final Sort array = arraySort.getSort(null, generic2);
		// select : ((Array X Y) X) -> Y
		declareInternalPolymorphicFunction("select", generic2, new Sort[] { array, generic2[0] }, generic2[1], 0);
		// store : ((Array X Y) X Y) -> (Array X Y)
		declareInternalPolymorphicFunction("store", generic2, new Sort[] { array, generic2[0], generic2[1] }, array, 0);
		// const : (Y) -> (Array X Y)
		declareInternalPolymorphicFunction("const", generic2, new Sort[] { generic2[1] },
				array, FunctionSymbol.INTERNAL | FunctionSymbol.RETURNOVERLOAD);
	}

	private void createBitVecSort() {
		mBitVecSort = new SortSymbol(this, "BitVec", 0, null, SortSymbol.INTERNAL | SortSymbol.INDEXED) {
			@Override
			public void checkArity(final BigInteger[] indices, final int arity) {
				if (indices == null || indices.length != 1) {
					throw new IllegalArgumentException("BitVec needs one index");
				}
				if (indices[0].signum() <= 0) {
					throw new IllegalArgumentException("BitVec index must be positive");
				}
				if (arity != 0) {
					throw new IllegalArgumentException("BitVec has no parameters");
				}
			}
		};
		mDeclaredSorts.put("BitVec", mBitVecSort);
	}

	private void createBitVecOperators() {
		class RegularBitVecFunction extends FunctionSymbolFactory {
			int mNumArgs;
			int mFlags;
			Sort mResult;

			public RegularBitVecFunction(final String name, final int numArgs, final Sort result, final int flags) {
				super(name);
				mNumArgs = numArgs;
				mResult = result;
				mFlags = flags;
			}

			public RegularBitVecFunction(final String name, final int numArgs, final Sort result) {
				this(name, numArgs, result, FunctionSymbol.INTERNAL);
			}

			@Override
			public int getFlags(final BigInteger[] indices, final Sort[] paramSorts, final Sort resultSort) {
				return mFlags;
			}

			@Override
			public Sort getResultSort(final BigInteger[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices != null || paramSorts.length != mNumArgs || resultSort != null
						|| paramSorts[0].getName() != "BitVec") {
					return null;
				}
				for (int i = 1; i < mNumArgs; i++) {
					if (paramSorts[i] != paramSorts[0]) {
						return null;
					}
				}
				return mResult == null ? paramSorts[0] : mResult;
			}
		}
		class ExtendBitVecFunction extends FunctionSymbolFactory {
			public ExtendBitVecFunction(final String name) {
				super(name);
			}

			@Override
			public Sort getResultSort(final BigInteger[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices == null || indices.length != 1 || paramSorts.length != 1 || resultSort != null
						|| paramSorts[0].getName() != "BitVec") {
					return null;
				}
				final BigInteger size = indices[0].add(paramSorts[0].getIndices()[0]);
				return mBitVecSort.getSort(new BigInteger[] { size }, new Sort[0]);
			}
		}
		class RotateBitVecFunction extends FunctionSymbolFactory {
			public RotateBitVecFunction(final String name) {
				super(name);
			}

			@Override
			public Sort getResultSort(final BigInteger[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices == null || indices.length != 1 || paramSorts.length != 1 || resultSort != null
						|| paramSorts[0].getName() != "BitVec") {
					return null;
				}
				return paramSorts[0];
			}
		}
		defineFunction(new FunctionSymbolFactory("concat") {
			@Override
			public int getFlags(final BigInteger[] indices, final Sort[] paramSorts, final Sort resultSort) {
				return FunctionSymbol.INTERNAL;
			}

			@Override
			public Sort getResultSort(final BigInteger[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices != null || paramSorts.length != 2 || resultSort != null
						|| paramSorts[0].getName() != "BitVec" || paramSorts[1].getName() != "BitVec") {
					return null;
				}
				final BigInteger size = paramSorts[0].getIndices()[0].add(paramSorts[1].getIndices()[0]);
				return mBitVecSort.getSort(new BigInteger[] { size }, new Sort[0]);
			}
		});
		defineFunction(new FunctionSymbolFactory("extract") {
			@Override
			public Sort getResultSort(final BigInteger[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices == null || indices.length < 2 || paramSorts.length != 1 || resultSort != null
						|| paramSorts[0].getName() != "BitVec") {
					return null;
				}
				if (indices[0].compareTo(indices[1]) < 0 || paramSorts[0].getIndices()[0].compareTo(indices[0]) < 0) {
					return null;
				}
				final BigInteger size = indices[0].subtract(indices[1]).add(BigInteger.ONE);
				return mBitVecSort.getSort(new BigInteger[] { size }, new Sort[0]);
			}
		});
		final Sort bitvec1 = mBitVecSort.getSort(new BigInteger[] { BigInteger.ONE }, new Sort[0]);

		defineFunction(new RegularBitVecFunction("bvnot", 1, null));
		defineFunction(new RegularBitVecFunction("bvand", 2, null, FunctionSymbol.INTERNAL | FunctionSymbol.LEFTASSOC));
		defineFunction(new RegularBitVecFunction("bvor", 2, null, FunctionSymbol.INTERNAL | FunctionSymbol.LEFTASSOC));
		defineFunction(new RegularBitVecFunction("bvneg", 1, null));
		defineFunction(new RegularBitVecFunction("bvadd", 2, null, FunctionSymbol.INTERNAL | FunctionSymbol.LEFTASSOC));
		defineFunction(new RegularBitVecFunction("bvmul", 2, null, FunctionSymbol.INTERNAL | FunctionSymbol.LEFTASSOC));
		defineFunction(new RegularBitVecFunction("bvudiv", 2, null));
		defineFunction(new RegularBitVecFunction("bvurem", 2, null));
		defineFunction(new RegularBitVecFunction("bvshl", 2, null));
		defineFunction(new RegularBitVecFunction("bvlshr", 2, null));

		defineFunction(new RegularBitVecFunction("bvnand", 2, null));
		defineFunction(new RegularBitVecFunction("bvnor", 2, null));
		defineFunction(new RegularBitVecFunction("bvxor", 2, null, FunctionSymbol.INTERNAL | FunctionSymbol.LEFTASSOC));
		defineFunction(new RegularBitVecFunction("bvxnor", 2, null));
		defineFunction(new RegularBitVecFunction("bvcomp", 2, bitvec1));
		defineFunction(new RegularBitVecFunction("bvsub", 2, null));
		defineFunction(new RegularBitVecFunction("bvsdiv", 2, null));
		defineFunction(new RegularBitVecFunction("bvsrem", 2, null));
		defineFunction(new RegularBitVecFunction("bvsmod", 2, null));
		defineFunction(new RegularBitVecFunction("bvashr", 2, null));

		defineFunction(new FunctionSymbolFactory("repeat") {
			@Override
			public Sort getResultSort(final BigInteger[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices == null || indices.length != 1 || paramSorts.length != 1 || resultSort != null
						|| paramSorts[0].getName() != "BitVec") {
					return null;
				}
				final BigInteger size = indices[0].multiply(paramSorts[0].getIndices()[0]);
				return mBitVecSort.getSort(new BigInteger[] { size }, new Sort[0]);
			}
		});
		defineFunction(new ExtendBitVecFunction("zero_extend"));
		defineFunction(new ExtendBitVecFunction("sign_extend"));
		defineFunction(new RotateBitVecFunction("rotate_left"));
		defineFunction(new RotateBitVecFunction("rotate_right"));

		defineFunction(new RegularBitVecFunction("bvult", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));
		defineFunction(new RegularBitVecFunction("bvule", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));
		defineFunction(new RegularBitVecFunction("bvugt", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));
		defineFunction(new RegularBitVecFunction("bvuge", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));
		defineFunction(new RegularBitVecFunction("bvslt", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));
		defineFunction(new RegularBitVecFunction("bvsle", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));
		defineFunction(new RegularBitVecFunction("bvsgt", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));
		defineFunction(new RegularBitVecFunction("bvsge", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));
	}

	private void createFloatingPointOperators() {

		mFloatingPointSort = new SortSymbol(this, "FloatingPoint", 0, null, SortSymbol.INTERNAL | SortSymbol.INDEXED) {
			@Override
			public void checkArity(final BigInteger[] indices, final int arity) {
				if (indices == null || indices.length != 2) {
					throw new IllegalArgumentException("Floating Point needs two indices");
				}

				if (indices[0].signum() <= 0 || indices[1].signum() <= 0) {
					throw new IllegalArgumentException("FloatingPoint indices must be greater 0");
				}

				if (arity != 0) {
					throw new IllegalArgumentException("FloatingPoint has no parameters");
				}
			}
		};

		mDeclaredSorts.put("FloatingPoint", mFloatingPointSort);
		mRoundingModeSort = declareInternalSort("RoundingMode", 0, 0).getSort(null, new Sort[0]);

		/*
		 * Used to create Functions of the Floating Point theory
		 */
		class RegularFloatingPointFunction extends FunctionSymbolFactory {
			int mNumArgs;
			Sort mResult;
			int mFlags;
			int mFirstFloat;

			public RegularFloatingPointFunction(final String name, final int numArgs, final Sort result,
					final int flags) {
				super(name);
				mNumArgs = numArgs;
				mResult = result;
				mFlags = flags;
			}

			@Override
			public int getFlags(final BigInteger[] indices, final Sort[] paramSorts, final Sort resultSort) {
				return mFlags;
			}

			@Override
			public Sort getResultSort(final BigInteger[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices != null || paramSorts.length != mNumArgs || resultSort != null) {
					return null;
				}
				if (paramSorts[0].getName() == ("RoundingMode")) {
					mFirstFloat = 1;
				} else {
					mFirstFloat = 0;
				}
				for (int i = mFirstFloat; i < mNumArgs; i++) {
					if (paramSorts[i].getName() != "FloatingPoint") {
						return null;
					}
				}
				return mResult == null ? paramSorts[mFirstFloat] : mResult;
			}
		}

		defineFunction(new FunctionSymbolFactory("fp") {
			@Override
			public Sort getResultSort(final BigInteger[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices != null || paramSorts.length != 3 || resultSort != null
						|| paramSorts[0].getName() != "BitVec" || !paramSorts[0].getIndices()[0].equals(BigInteger.ONE)
						|| paramSorts[1].getName() != "BitVec" || paramSorts[2].getName() != "BitVec") {
					return null;
				}
				final BigInteger[] fpIndices = new BigInteger[2];
				fpIndices[0] = paramSorts[1].getIndices()[0];
				fpIndices[1] = paramSorts[2].getIndices()[0].add(BigInteger.ONE);
				return mFloatingPointSort.getSort(fpIndices, new Sort[0]);
			}
		});

		// from BitVec to FP
		defineFunction(new FunctionSymbolFactory("to_fp") {
			@Override
			public Sort getResultSort(final BigInteger[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices == null || indices.length != 2 || paramSorts == null) {
					return null;
				}
				// from BitVec to FP
				if (paramSorts.length == 1 && paramSorts[0].getName() == "BitVec") {
					if (!((indices[0].add(indices[1]).equals(paramSorts[0].getIndices()[0])))) {
						return null;
					}
					return mFloatingPointSort.getSort(indices, new Sort[0]);
				}

				// from FP to FP
				if (paramSorts.length == 2 && paramSorts[0].getName() == "RoundingMode"
						&& (paramSorts[1].getName() == "FloatingPoint")) {
					return mFloatingPointSort.getSort(indices, new Sort[0]);
				}

				// from real to FP
				if (paramSorts.length == 2 && paramSorts[0].getName() == "RoundingMode"
						&& paramSorts[1].getName() == "Real") {
					return mFloatingPointSort.getSort(indices, new Sort[0]);
				}

				// from signed machine integer, represented as a 2's complement bit vector to FP
				if (paramSorts.length == 2 && paramSorts[0].getName() == "RoundingMode"
						&& paramSorts[1].getName() == "BitVec") {
					return mFloatingPointSort.getSort(indices, new Sort[0]);
				}
				return null;
			}
		});

		defineFunction(new FunctionSymbolFactory("to_fp_unsigned") {
			@Override
			public Sort getResultSort(final BigInteger[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices == null || indices.length != 2 || paramSorts.length != 2 || resultSort != null
						|| paramSorts[0].getName() != "RoundingMode" || paramSorts[1].getName() != "BitVec") {
					return null;
				}
				return mFloatingPointSort.getSort(indices, new Sort[0]);
			}
		});

		defineFunction(new FunctionSymbolFactory("fp.to_ubv") {
			@Override
			public Sort getResultSort(final BigInteger[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices == null || indices.length != 1 || paramSorts.length != 2 || resultSort != null
						|| paramSorts[0].getName() != "RoundingMode" || paramSorts[1].getName() != "FloatingPoint") {
					return null;
				}
				return mBitVecSort.getSort(new BigInteger[] { indices[0] }, new Sort[0]);
			}
		});

		defineFunction(new FunctionSymbolFactory("fp.to_sbv") {
			@Override
			public Sort getResultSort(final BigInteger[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices == null || indices.length != 1 || paramSorts.length != 2 || resultSort != null
						|| paramSorts[0].getName() != "RoundingMode" || paramSorts[1].getName() != "FloatingPoint") {
					return null;
				}
				return mBitVecSort.getSort(new BigInteger[] { indices[0] }, new Sort[0]);
			}
		});

		/*
		 * Used to create Constants of the Floating Point theory
		 */
		class FloatingPointConstant extends FunctionSymbolFactory {
			public FloatingPointConstant(final String name) {
				super(name);
			}

			@Override
			public Sort getResultSort(final BigInteger[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices.length != 2 || paramSorts.length != 0 || resultSort != null) {
					return null;
				}
				return mFloatingPointSort.getSort(indices, new Sort[0]);
			}
		}
		// +/- infinity
		defineFunction(new FloatingPointConstant("+oo"));
		defineFunction(new FloatingPointConstant("-oo"));
		// +/- zero
		defineFunction(new FloatingPointConstant("+zero"));
		defineFunction(new FloatingPointConstant("-zero"));

		defineFunction(new FloatingPointConstant("NaN"));

		// short forms of common floats
		defineSort("Float16", 0,
				mFloatingPointSort.getSort(new BigInteger[] { new BigInteger("5"), new BigInteger("11") }));
		defineSort("Float32", 0,
				mFloatingPointSort.getSort(new BigInteger[] { new BigInteger("8"), new BigInteger("24") }));
		defineSort("Float64", 0,
				mFloatingPointSort.getSort(new BigInteger[] { new BigInteger("11"), new BigInteger("53") }));
		defineSort("Float128", 0,
				mFloatingPointSort.getSort(new BigInteger[] { new BigInteger("15"), new BigInteger("113") }));

		// RoundingModes
		declareInternalFunction("roundNearestTiesToEven", new Sort[0], mRoundingModeSort, 0);
		declareInternalFunction("roundNearestTiesToAway", new Sort[0], mRoundingModeSort, 0);
		declareInternalFunction("roundTowardPositive", new Sort[0], mRoundingModeSort, 0);
		declareInternalFunction("roundTowardNegative", new Sort[0], mRoundingModeSort, 0);
		declareInternalFunction("roundTowardZero", new Sort[0], mRoundingModeSort, 0);
		defineFunction("RNE", new Sort[0], mRoundingModeSort, new TermVariable[0], term("roundNearestTiesToEven"),
				FunctionSymbol.INTERNAL);
		defineFunction("RNA", new Sort[0], mRoundingModeSort, new TermVariable[0], term("roundNearestTiesToAway"),
				FunctionSymbol.INTERNAL);
		defineFunction("RTP", new Sort[0], mRoundingModeSort, new TermVariable[0], term("roundTowardPositive"),
				FunctionSymbol.INTERNAL);
		defineFunction("RTN", new Sort[0], mRoundingModeSort, new TermVariable[0], term("roundTowardNegative"),
				FunctionSymbol.INTERNAL);
		defineFunction("RTZ", new Sort[0], mRoundingModeSort, new TermVariable[0], term("roundTowardZero"),
				FunctionSymbol.INTERNAL);

		// Operators
		defineFunction(new RegularFloatingPointFunction("fp.abs", 1, null, FunctionSymbol.INTERNAL));
		defineFunction(new RegularFloatingPointFunction("fp.neg", 1, null, FunctionSymbol.INTERNAL));
		defineFunction(new RegularFloatingPointFunction("fp.min", 2, null, FunctionSymbol.INTERNAL));
		defineFunction(new RegularFloatingPointFunction("fp.max", 2, null, FunctionSymbol.INTERNAL));
		defineFunction(new RegularFloatingPointFunction("fp.rem", 2, null, FunctionSymbol.INTERNAL));
		// rounded operators
		defineFunction(new RegularFloatingPointFunction("fp.add", 3, null, FunctionSymbol.INTERNAL));
		defineFunction(new RegularFloatingPointFunction("fp.sub", 3, null, FunctionSymbol.INTERNAL));
		defineFunction(new RegularFloatingPointFunction("fp.mul", 3, null, FunctionSymbol.INTERNAL));
		defineFunction(new RegularFloatingPointFunction("fp.div", 3, null, FunctionSymbol.INTERNAL));
		defineFunction(new RegularFloatingPointFunction("fp.fma", 4, null, FunctionSymbol.INTERNAL));
		defineFunction(new RegularFloatingPointFunction("fp.sqrt", 2, null, FunctionSymbol.INTERNAL));
		defineFunction(new RegularFloatingPointFunction("fp.roundToIntegral", 2, null, FunctionSymbol.INTERNAL));

		// Comparison Operators
		defineFunction(new RegularFloatingPointFunction("fp.leq", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));
		defineFunction(new RegularFloatingPointFunction("fp.lt", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));
		defineFunction(new RegularFloatingPointFunction("fp.geq", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));
		defineFunction(new RegularFloatingPointFunction("fp.gt", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));
		defineFunction(new RegularFloatingPointFunction("fp.eq", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));

		// Classification of numbers
		defineFunction(new RegularFloatingPointFunction("fp.isNormal", 1, mBooleanSort, FunctionSymbol.INTERNAL));
		defineFunction(new RegularFloatingPointFunction("fp.isSubnormal", 1, mBooleanSort, FunctionSymbol.INTERNAL));
		defineFunction(new RegularFloatingPointFunction("fp.isZero", 1, mBooleanSort, FunctionSymbol.INTERNAL));
		defineFunction(new RegularFloatingPointFunction("fp.isInfinite", 1, mBooleanSort, FunctionSymbol.INTERNAL));
		defineFunction(new RegularFloatingPointFunction("fp.isNaN", 1, mBooleanSort, FunctionSymbol.INTERNAL));
		defineFunction(new RegularFloatingPointFunction("fp.isNegative", 1, mBooleanSort, FunctionSymbol.INTERNAL));
		defineFunction(new RegularFloatingPointFunction("fp.isPositive", 1, mBooleanSort, FunctionSymbol.INTERNAL));

		// Conversion from FP
		defineFunction(new RegularFloatingPointFunction("fp.to_real", 1, mRealSort, FunctionSymbol.INTERNAL));
	}

	private void setLogic(final Logics logic) {
		mLogic = logic;

		if (logic.isArray()) {
			createArrayOperators();
		}

		if (logic.hasReals() || logic.isFloatingPoint()) {
			mRealSort = declareInternalSort("Real", 0, SortSymbol.NUMERIC).getSort(null, new Sort[0]);
		}

		if (logic.isArithmetic()) {

			if (logic.hasIntegers()) {
				mNumericSort = declareInternalSort("Int", 0, SortSymbol.NUMERIC).getSort(null, new Sort[0]);
			} else {
				mNumericSort = mRealSort;
			}

			if (logic.isIRA()) {
				createIRAOperators();
			} else {
				createNumericOperators(mNumericSort, logic.hasReals());
			}
		}

		if (logic.isBitVector() || logic.isFloatingPoint()) {
			createBitVecSort();
		}

		if (logic.isBitVector()) {
			createBitVecOperators();
		}

		if (logic.isFloatingPoint()) {
			createFloatingPointOperators();
		}
		if (mSolverSetup != null) {
			mSolverSetup.setLogic(this, logic);
		}
	}

	/******************** SORTS ********************************************/

	private SortSymbol defineSort(final String name, final int paramCount, final Sort definition, final int flags) {
		if ((flags & FunctionSymbol.INTERNAL) == 0 && definition == null && !mLogic.isUF() && !mLogic.isArray()) {
			throw new IllegalArgumentException("Free sorts are not allowed in this logic");
		}
		SortSymbol sortsym = mDeclaredSorts.get(name);
		if (sortsym != null) {
			throw new IllegalArgumentException("Sort " + name + " already exists.");
		}
		sortsym = new SortSymbol(this, name, paramCount, definition, flags);
		mDeclaredSorts.put(name, sortsym);
		return sortsym;
	}

	public SortSymbol declareSort(final String name, final int paramCount) {
		return defineSort(name, paramCount, null, 0);
	}

	public SortSymbol defineSort(final String name, final int paramCount, final Sort definition) {
		return defineSort(name, paramCount, definition, 0);
	}

	public Sort[] createSortVariables(final String... names) {
		final Sort[] sorts = new Sort[names.length];
		for (int i = 0; i < names.length; i++) {
			sorts[i] = new SortSymbol(this, names[i], i, null, SortSymbol.TYPEPARAM).getSort(null, new Sort[0]);
		}
		return sorts;
	}

	public SortSymbol declareInternalSort(final String name, final int paramCount, final int flags) {
		return defineSort(name, paramCount, null, flags | SortSymbol.INTERNAL);
	}

	/**
	 * Returns the sort object for a previously declared or defined sort with sort arguments.
	 *
	 * @param id
	 *            The name of the sort.
	 * @param args
	 *            The sort arguments.
	 * @return the sort object.
	 */
	public Sort getSort(final String id, final Sort... args) {
		return getSort(id, null, args);
	}

	/**
	 * Returns the sort object for a previously declared or defined sort with sort arguments.
	 *
	 * @param id
	 *            The name of the sort.
	 * @param args
	 *            The sort arguments.
	 * @return the sort object.
	 */
	public Sort getSort(final String id, final BigInteger[] indices, final Sort... args) {
		SortSymbol symbol;
		symbol = mDeclaredSorts.get(id);
		if (symbol == null) {
			return null;
		}
		return symbol.getSort(indices, args);
	}

	/**
	 * Returns the Boolean sort. This is more efficient but has the same effect as calling getSort("Bool").
	 *
	 * @return the Boolean sort.
	 */
	public Sort getBooleanSort() {
		return mBooleanSort;
	}

	/**
	 * Get the sort used to construct integers. Note that this returns <code>null</code> if the logic does not support
	 * integers.
	 *
	 * @return Sort used for integers.
	 */
	public Sort getNumericSort() {
		return mNumericSort;
	}

	/**
	 * Get the sort used to construct reals. Note that this returns <code>null</code> if the logic does not support
	 * reals.
	 *
	 * @return Sort used for reals.
	 */
	public Sort getRealSort() {
		return mRealSort;
	}

	/**
	 * Get the sort used to construct strings. Note that this returns <code>null</code> if the logic does not support
	 * strings.
	 *
	 * @return Sort used for strings.
	 */
	public Sort getStringSort() {
		return mStringSort;
	}

	/******************** FUNCTIONS SYMBOLS AND FUNCTION TERMS ************/

	private void defineFunction(final FunctionSymbolFactory factory) {
		if (mFunFactory.put(factory.mFuncName, factory) != null) {
			throw new AssertionError();
		}
	}

	private FunctionSymbol defineFunction(final String name, Sort[] paramTypes, final Sort resultType,
			TermVariable[] definitionVars, final Term definition, final int flags) {
		if ((flags & FunctionSymbol.INTERNAL) == 0) {
			if (mLogic == null) {
				throw new IllegalArgumentException("Call set-logic first!");
			}
			if (!mLogic.isUF() && paramTypes.length > 0 && definition == null) {
				throw new IllegalArgumentException("Free functions are not allowed in this logic!");
			}
		}
		if (name.charAt(0) == '@' && name.matches(MODEL_VALUE_PATTERN)) {
			throw new IllegalArgumentException("Function " + name + " is reserved for internal purposes.");
		}
		if (mFunFactory.get(name) != null || mDeclaredFuns.get(name) != null) {
			throw new IllegalArgumentException("Function " + name + " is already defined.");
		}
		if (paramTypes.length == 0) {
			paramTypes = EMPTY_SORT_ARRAY;
		}
		if (definitionVars != null && definitionVars.length == 0) {
			definitionVars = EMPTY_TERM_VARIABLE_ARRAY;
		}
		final FunctionSymbol f =
				new FunctionSymbol(name, null, paramTypes, resultType, definitionVars, definition, flags);
		mDeclaredFuns.put(name, f);
		return f;
	}

	/**
	 * Declare a new function symbol. This corresponds to declare-fun in SMTLIB.
	 *
	 * @param name
	 *            name of the function.
	 * @param paramTypes
	 *            the sorts of the parameters of the function.
	 * @param resultType
	 *            the sort of the result type of the function.
	 * @throws IllegalArgumentException
	 *             if a function with that name is already defined or if the sorts are not visible in this scope.
	 * @return the created function symbol.
	 */
	public FunctionSymbol declareFunction(final String name, final Sort[] paramTypes, final Sort resultType) {
		return defineFunction(name, paramTypes, resultType, null, null, 0);
	}

	/**
	 * Defines a new function symbol. This corresponds to define-fun in SMTLIB.
	 *
	 * @param name
	 *            name of the function.
	 * @param definitionVars
	 *            the variables of the function.
	 * @param definition
	 *            the definition of the function.
	 * @throws IllegalArgumentException
	 *             if a function with that name is already defined or if the sorts are not visible in this scope.
	 * @return the created function symbol.
	 */
	public FunctionSymbol defineFunction(final String name, final TermVariable[] definitionVars,
			final Term definition) {
		final Sort[] paramTypes = definitionVars.length == 0 ? EMPTY_SORT_ARRAY : new Sort[definitionVars.length];
		for (int i = 0; i < paramTypes.length; i++) {
			paramTypes[i] = definitionVars[i].getSort();
		}
		final Sort resultType = definition.getSort();
		return defineFunction(name, paramTypes, resultType, definitionVars, definition, 0);
	}

	public FunctionSymbol getFunction(final String name, final Sort... paramTypes) {
		return getFunctionWithResult(name, null, null, paramTypes);
	}

	public Map<String, FunctionSymbol> getDeclaredFunctions() {
		return mDeclaredFuns;
	}

	private FunctionSymbol getModelValueSymbol(final String name, final Sort sort) {
		final int hash = HashUtils.hashJenkins(name.hashCode(), sort);
		for (final FunctionSymbol symb : mModelValueCache.iterateHashCode(hash)) {
			if (symb.getName().equals(name) && symb.getReturnSort() == sort) {
				return symb;
			}
		}
		final FunctionSymbol symb = new FunctionSymbol(name, null, EMPTY_SORT_ARRAY, sort, null, null,
				FunctionSymbol.RETURNOVERLOAD | FunctionSymbol.INTERNAL | FunctionSymbol.MODELVALUE);
		mModelValueCache.put(hash, symb);
		return symb;
	}

	public FunctionSymbol getFunctionWithResult(final String name, final BigInteger[] indices, final Sort resultType,
			final Sort... paramTypes) {
		if (resultType != null && indices == null && paramTypes.length == 0 && name.matches(MODEL_VALUE_PATTERN)) {
			return getModelValueSymbol(name, resultType);
		}
		final FunctionSymbolFactory factory = mFunFactory.get(name);
		if (factory != null) {
			final FunctionSymbol fsym = factory.getFunctionWithResult(this, indices, paramTypes, resultType);
			if (fsym != null) {
				return fsym;
			}
		} else {
			final FunctionSymbol fsym = mDeclaredFuns.get(name);
			if (fsym != null && indices == null && resultType == null && fsym.typecheck(paramTypes)) {
				return fsym;
			}
		}
		if (mIRAWrappers != null) {
			final FunctionSymbol fsym = mIRAWrappers.createWrapper(this, name, indices, paramTypes, resultType);
			if (fsym != null)
				return fsym;
		}
		if (mBitVecSort != null && name.matches(BITVEC_CONST_PATTERN) && indices != null && indices.length == 1
				&& resultType == null) {
			/* Create bitvector constants */
			return getBitVecConstant(name, indices);
		}
		return null;
	}

	private FunctionSymbol getBitVecConstant(final String name, final BigInteger[] indices) {
		if (mBitVecConstCache == null) {
			mBitVecConstCache = new UnifyHash<>();
		}
		final int hash = HashUtils.hashJenkins(name.hashCode(), (Object[]) indices);
		for (final FunctionSymbol symb : mBitVecConstCache.iterateHashCode(hash)) {
			if (symb.getName().equals(name) && symb.getIndices()[0].equals(indices[0])) {
				return symb;
			}
		}
		final Sort sort = mBitVecSort.getSort(indices);
		final FunctionSymbol symb =
				new FunctionSymbol(name, indices, EMPTY_SORT_ARRAY, sort, null, null, FunctionSymbol.INTERNAL);
		mBitVecConstCache.put(hash, symb);
		return symb;
	}

	public ApplicationTerm term(final FunctionSymbolFactory factory, final Term... parameters) {
		final Sort[] sorts = parameters.length == 0 ? EMPTY_SORT_ARRAY : new Sort[parameters.length];
		for (int i = 0; i < parameters.length; i++) {
			sorts[i] = parameters[i].getSort();
		}
		final FunctionSymbol fsym = factory.getFunctionWithResult(this, null, sorts, null);
		if (fsym == null) {
			throw new IllegalArgumentException("Did not find overload for function " + factory);
		}
		return term(fsym, parameters);
	}

	public ApplicationTerm term(final String func, final Term... parameters) {
		final Sort[] paramSorts = parameters.length == 0 ? EMPTY_SORT_ARRAY : new Sort[parameters.length];
		for (int i = 0; i < parameters.length; i++) {
			paramSorts[i] = parameters[i].getSort();
		}
		final FunctionSymbol fsym = getFunctionWithResult(func, null, null, paramSorts);
		if (fsym == null) {
			return null;
		}
		return term(fsym, parameters);
	}

	public ApplicationTerm term(final FunctionSymbol func, Term... parameters) {
		if (parameters.length == 0) {
			parameters = EMPTY_TERM_ARRAY;
		}
		final int hash = ApplicationTerm.hashApplication(func, parameters);
		for (final Term t : mTermCache.iterateHashCode(hash)) {
			if (t instanceof ApplicationTerm) {
				final ApplicationTerm app = (ApplicationTerm) t;
				if (func == app.getFunction() && Arrays.equals(app.getParameters(), parameters)) {
					return app;
				}
			}
		}
		final ApplicationTerm app = new ApplicationTerm(func, parameters, hash);
		mTermCache.put(hash, app);
		return app;
	}

	/******************** TERM VARIABLES AND VARIABLE TERMS *****************/

	/**
	 * Create a fresh term variable that does not clash with any existing one.
	 *
	 * @param prefix
	 *            the prefix of the variable name (without the leading ?).
	 * @param sort
	 *            the sort of the variable.
	 * @return a fresh term variable.
	 */
	public TermVariable createFreshTermVariable(final String prefix, final Sort sort) {
		final String name = "." + prefix + "." + mTvarCtr++;
		return new TermVariable(name, sort, TermVariable.hashVariable(name, sort));
	}

	/**
	 * Create a term variable with the given name and sort.
	 *
	 * @param name
	 *            the variable name.
	 * @param sort
	 *            the sort of the variable.
	 * @return a term variable.
	 */
	public TermVariable createTermVariable(final String name, final Sort sort) {
		final int hash = TermVariable.hashVariable(name, sort);
		for (final TermVariable tv : mTvUnify.iterateHashCode(hash)) {
			if (tv.getSort().equals(sort) && tv.getName().equals(name)) {
				return tv;
			}
		}
		final TermVariable tv = new TermVariable(name, sort, hash);
		mTvUnify.put(hash, tv);
		return tv;
	}

	public Term term(final TermVariable var) {
		return var;
	}

	/******************** ANNOTATED TERMS *********************************/

	public Term annotatedTerm(final Annotation[] annots, final Term sub) {
		final int hash = AnnotatedTerm.hashAnnotations(annots, sub);
		for (final Term t : mTermCache.iterateHashCode(hash)) {
			if (t instanceof AnnotatedTerm) {
				final AnnotatedTerm annot = (AnnotatedTerm) t;
				if (sub == annot.getSubterm() && Arrays.equals(annot.getAnnotations(), annots)) {
					return annot;
				}
			}
		}
		final AnnotatedTerm annot = new AnnotatedTerm(annots, sub, hash);
		mTermCache.put(hash, annot);
		return annot;
	}

	/******************** ASSERTION STACK *********************************/

	public void push() {
		if (!mGlobalDecls) {
			mDeclaredFuns.beginScope();
			mDeclaredSorts.beginScope();
		}
	}

	public void pop() {
		if (!mGlobalDecls) {
			mDeclaredFuns.endScope();
			mDeclaredSorts.endScope();
		}
	}

	/******************** SKOLEMIZATION SUPPORT ***************************/
	public FunctionSymbol skolemize(final TermVariable tv) {
		return new FunctionSymbol("@" + tv.getName() + "_skolem_" + mSkolemCounter++, null, EMPTY_SORT_ARRAY,
				tv.getSort(), null, null, 0);
	}

	public void resetAssertions() {
		if (mGlobalDecls) {
			return;
		}
		while (mDeclaredFuns.getActiveScopeNum() > 1) {
			mDeclaredFuns.endScope();
		}
		for (final Iterator<Map.Entry<String, FunctionSymbol>> it = mDeclaredFuns.entrySet().iterator(); it
				.hasNext();) {
			final Map.Entry<String, FunctionSymbol> next = it.next();
			if (!next.getValue().isIntern()) {
				it.remove();
			}
		}
		while (mDeclaredSorts.getActiveScopeNum() > 1) {
			mDeclaredSorts.endScope();
		}
		for (final Iterator<Map.Entry<String, SortSymbol>> it = mDeclaredSorts.entrySet().iterator(); it.hasNext();) {
			final Map.Entry<String, SortSymbol> next = it.next();
			if (!next.getValue().isIntern()) {
				it.remove();
			}
		}
	}

	public void setGlobalSymbols(final boolean globalDecls) {
		mGlobalDecls = globalDecls;
	}
}
