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
			theory.declareInternalFunctionFactory(factory);
		}
	}

	private SolverSetup mSolverSetup;
	private Logics mLogic;
	private Sort mNumericSort, mRealSort, mStringSort, mBooleanSort;
	private SortSymbol mBitVecSort, mFloatingPointSort;
	private Sort mRoundingModeSort;
	private final ScopedHashMap<String, FunctionSymbolFactory> mFunFactory = new ScopedHashMap<>();
	private final UnifyHash<FunctionSymbol> mModelValueCache = new UnifyHash<>();

	private final ScopedHashMap<String, SortSymbol> mDeclaredSorts = new ScopedHashMap<>();
	private final ScopedHashMap<String, FunctionSymbol> mDeclaredFuns = new ScopedHashMap<>();

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

	private int mAuxCounter = 0;

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
		declareInternalPolymorphicFunction("ite", generic1, new Sort[] { mBooleanSort, generic1[0], generic1[0] },
				generic1[0], 0);
		mTrue = (ApplicationTerm) term(declareInternalFunction("true", noarg, mBooleanSort, 0));
		mFalse = (ApplicationTerm) term(declareInternalFunction("false", noarg, mBooleanSort, 0));
		declareInternalSort(SMTLIBConstants.FUNC, 2, SortSymbol.FUNCTION);

		// Finally, declare logic specific functions
		setLogic(logic);
	}

	/**
	 * Method to check if indices is a numeral or symbol. If numeral return as BigInteger, if symbol return null
	 */
	public BigInteger toNumeral(final String index) {
		try {
			return new BigInteger(index);
		} catch (final NumberFormatException e) {
			throw new SMTLIBException("not a numeral: " + index, e);
		}
	}

	/**
	 * Method to check if the parameter is the name of a constructor. If so, return the constructor.
	 */
	public FunctionSymbol getFunctionSymbol(final String constructor) {
		return mDeclaredFuns.get(constructor);
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

	public Term lambda(final TermVariable[] vars, final Term subterm) {
		final int hash = LambdaTerm.hashLambda(vars, subterm);
		for (final Term term : mTermCache.iterateHashCode(hash)) {
			if (term instanceof LambdaTerm) {
				final LambdaTerm lambda = (LambdaTerm) term;
				if (lambda.getSubterm() == subterm && Arrays.equals(lambda.getVariables(), vars)) {
					return lambda;
				}
			}
		}
		final LambdaTerm lambda = new LambdaTerm(vars, subterm, hash);
		mTermCache.put(hash, lambda);
		return lambda;
	}

	private Term quantify(final int quant, final TermVariable[] vars, final Term f) {
		final int hash = QuantifiedFormula.hashQuantifier(quant, vars, f);
		for (final Term term : mTermCache.iterateHashCode(hash)) {
			if (term instanceof QuantifiedFormula) {
				final QuantifiedFormula qf = (QuantifiedFormula) term;
				if (qf.getQuantifier() == quant && qf.getSubformula() == f && Arrays.equals(vars, qf.getVariables())) {
					return qf;
				}
			}
		}
		final QuantifiedFormula qf = new QuantifiedFormula(quant, vars, f, hash);
		mTermCache.put(hash, qf);
		return qf;
	}

	public Term exists(final TermVariable[] vars, final Term f) {
		return quantify(QuantifiedFormula.EXISTS, vars, f);
	}

	public Term forall(final TermVariable[] vars, final Term f) {
		return quantify(QuantifiedFormula.FORALL, vars, f);
	}

	public Term match(final Term dataArg, final TermVariable[][] vars, final Term[] cases,
			final DataType.Constructor[] constructors) {

		final int hash = MatchTerm.hashMatch(dataArg, vars, cases);
		for (final Term t : mTermCache.iterateHashCode(hash)) {
			if (t instanceof MatchTerm) {
				final MatchTerm mt = (MatchTerm) t;
				if (mt.getDataTerm() == dataArg && Arrays.equals(mt.getCases(), cases)
						&& Arrays.deepEquals(mt.getVariables(), vars)
						&& Arrays.equals(mt.getConstructors(), constructors)) {
					return mt;
				}
			}
		}
		final MatchTerm mt = new MatchTerm(hash, dataArg, vars, cases, constructors);
		mTermCache.put(hash, mt);
		return mt;
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
		if (mNumericSort != mRealSort) {
			// For integer sort, always use Rational constants for numerals.
			return constant(Rational.valueOf(num, BigInteger.ONE), mNumericSort);
		}
		// For real arithmetic using Rational would convert to decimal, which we want to avoid.
		// positive and negated numerals are represented as constants of BigInteger type
		// instead.
		return constant(num, mNumericSort);
	}

	public Term numeral(final String num) {
		return numeral(toNumeral(num));
	}

	public Term decimal(final BigDecimal value) {
		// Check if this is uses the default scale and no fractional part.
		// In this case we create a rational constant instead.
		// Also handle BigDecimal without scale to distinguish them from numerals.
		if (value.scale() <= 0 || (value.scale() == 1 && value.remainder(BigDecimal.ONE).signum() == 0)) {
			return constant(Rational.valueOf(value.toBigIntegerExact(), BigInteger.ONE), mRealSort);
		}
		// If the input contains something like 0.1, don't automatically convert to (/ 1.0 10.0), to avoid
		// changing the input.
		Term result = constant(value.abs(), mRealSort);
		// positive non-normalized decimals are represented as BigDecimal constants
		// negative BigDecimals like -0.1 are normalized to the SMT term (- 0.1)
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
		return constant(c, sort);
	}

	public Term binary(final String value) {
		assert value.startsWith("#b");
		if (mBitVecSort == null) {
			return null;
		}
		final String bsize = String.valueOf(value.length() - 2);
		final Sort sort = mBitVecSort.getSort(new String[] { bsize }, new Sort[0]);
		return new ConstantTerm(value, sort, ConstantTerm.hashConstant(value, sort));
	}

	public Term hexadecimal(final String value) {
		assert value.startsWith("#x");
		if (mBitVecSort == null) {
			return null;
		}
		final String bsize = String.valueOf(4 * (value.length() - 2));// NOCHECKSTYLE
		final Sort sort = mBitVecSort.getSort(new String[] { bsize }, new Sort[0]);
		return new ConstantTerm(value, sort, ConstantTerm.hashConstant(value, sort));
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

	public Term string(final QuotedObject value) {
		return constant(value, mStringSort);
	}

	/******************** LOGICS AND THEORIES ********************************/
	public Logics getLogic() {
		return mLogic;
	}

	public FunctionSymbol declareInternalFunction(final String name, final Sort[] paramTypes, final Sort resultType,
			final int flags) {
		return defineFunction(name, paramTypes, resultType, null, null, flags | FunctionSymbol.INTERNAL);
	}

	public FunctionSymbol declareInternalFunction(final String name, final Sort[] paramTypes,
			final TermVariable[] defVars, final Term definition, final int flags) {
		return defineFunction(name, paramTypes, definition.getSort(), defVars, definition,
				flags | FunctionSymbol.INTERNAL);
	}

	public PolymorphicFunctionSymbol declareInternalPolymorphicFunction(final String name, final Sort[] sortParams,
			final Sort[] paramTypes, final Sort resultType, final int flags) {
		assert !mFunFactory.containsKey(name);
		final PolymorphicFunctionSymbol f = new PolymorphicFunctionSymbol(name, sortParams, paramTypes, resultType,
				flags | FunctionSymbol.INTERNAL);
		declareInternalFunctionFactory(f);
		return f;
	}

	class MinusFunctionFactory extends FunctionSymbolFactory {
		Sort mSort1, mSort2;

		public MinusFunctionFactory(final Sort sort1, final Sort sort2) {
			super(SMTLIBConstants.MINUS);
			mSort1 = sort1;
			mSort2 = sort2;
		}

		@Override
		public int getFlags(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
			return paramSorts.length == 1 ? FunctionSymbol.INTERNAL
					: FunctionSymbol.LEFTASSOC | FunctionSymbol.INTERNAL;
		}

		@Override
		public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
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
		public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
			return indices != null && indices.length == 1 && toNumeral(indices[0]).signum() > 0
					&& paramSorts.length == 1 && paramSorts[0] == mNumericSort && resultSort == null ? mBooleanSort
							: null;
		}
	}

	private Term absDefinition(final TermVariable x) {
		final Term zero = Rational.ZERO.toTerm(x.getSort());
		return term(SMTLIBConstants.ITE, term(SMTLIBConstants.LT, x, zero), term(SMTLIBConstants.MINUS, x), x);
	}

	private void createNumericOperators(final Sort sort, final boolean isRealArith) {
		final Sort[] sort1 = new Sort[] { sort };
		final Sort[] sort2 = new Sort[] { sort, sort };
		declareInternalFunction(SMTLIBConstants.PLUS, sort2, sort, FunctionSymbol.LEFTASSOC);
		declareInternalFunctionFactory(new MinusFunctionFactory(sort, sort));
		declareInternalFunction(SMTLIBConstants.MUL, sort2, sort, FunctionSymbol.LEFTASSOC);
		/* the functions /, div and mod are partial (for division by 0) and thus partially uninterpreted */
		if (isRealArith) {
			declareInternalFunction(SMTLIBConstants.DIVIDE, sort2, sort,
					FunctionSymbol.LEFTASSOC | FunctionSymbol.UNINTERPRETEDINTERNAL);
		} else {
			declareInternalFunction(SMTLIBConstants.DIV, sort2, sort,
					FunctionSymbol.LEFTASSOC | FunctionSymbol.UNINTERPRETEDINTERNAL);
			declareInternalFunction(SMTLIBConstants.MOD, sort2, sort, FunctionSymbol.UNINTERPRETEDINTERNAL);
			declareInternalFunctionFactory(new DivisibleFunctionFactory());
		}
		final Sort sBool = mBooleanSort;
		declareInternalFunction(SMTLIBConstants.GT, sort2, sBool, FunctionSymbol.CHAINABLE);
		declareInternalFunction(SMTLIBConstants.GEQ, sort2, sBool, FunctionSymbol.CHAINABLE);
		declareInternalFunction(SMTLIBConstants.LT, sort2, sBool, FunctionSymbol.CHAINABLE);
		declareInternalFunction(SMTLIBConstants.LEQ, sort2, sBool, FunctionSymbol.CHAINABLE);

		final TermVariable x = createTermVariable("x", sort);
		declareInternalFunction(SMTLIBConstants.ABS, sort1, new TermVariable[] { x }, absDefinition(x), 0);
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
			public int getFlags(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
				return mFlags;
			}

			@Override
			public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices == null && paramSorts.length == 2 && paramSorts[0] == paramSorts[1]
						&& (paramSorts[0] == mNumericSort || paramSorts[0] == mRealSort) && resultSort == null) {
					return mReturnSort == null ? paramSorts[0] : mReturnSort;
				}
				return null;
			}
		}

		declareInternalFunctionFactory(new BinArithFactory("+", null, FunctionSymbol.LEFTASSOC));
		declareInternalFunctionFactory(new MinusFunctionFactory(mNumericSort, mRealSort));
		declareInternalFunctionFactory(new BinArithFactory("*", null, FunctionSymbol.LEFTASSOC));
		declareInternalFunctionFactory(new BinArithFactory(">", mBooleanSort, FunctionSymbol.CHAINABLE));
		declareInternalFunctionFactory(new BinArithFactory(">=", mBooleanSort, FunctionSymbol.CHAINABLE));
		declareInternalFunctionFactory(new BinArithFactory("<", mBooleanSort, FunctionSymbol.CHAINABLE));
		declareInternalFunctionFactory(new BinArithFactory("<=", mBooleanSort, FunctionSymbol.CHAINABLE));

		final Sort[] int1 = new Sort[] { mNumericSort };
		final Sort[] int2 = new Sort[] { mNumericSort, mNumericSort };
		final Sort[] real1 = new Sort[] { mRealSort };
		final Sort[] real2 = new Sort[] { mRealSort, mRealSort };
		declareInternalFunction("/", real2, mRealSort, FunctionSymbol.LEFTASSOC);
		declareInternalFunction("div", int2, mNumericSort, FunctionSymbol.LEFTASSOC);
		declareInternalFunctionFactory(new DivisibleFunctionFactory());
		declareInternalFunction("to_real", int1, mRealSort, 0);
		declareInternalFunction("to_int", real1, mNumericSort, 0);

		declareInternalFunction("mod", int2, mNumericSort, 0);
		final TermVariable xr = createTermVariable("x1", mRealSort);
		// isint x: (= x (to_real (to_int x)))
		final Term isintx = term("=", xr, term("to_real", term("to_int", xr)));
		declareInternalFunction("is_int", real1, new TermVariable[] { xr }, isintx, 0);

		declareInternalFunctionFactory(new FunctionSymbolFactory("abs") {
			@Override
			public Term getDefinition(final TermVariable[] tvs, final Sort resultSort) {
				return absDefinition(tvs[0]);
			}

			@Override
			public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
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
		declareInternalPolymorphicFunction(SMTLIBConstants.CONST, generic2, new Sort[] { generic2[1] }, array,
				FunctionSymbol.INTERNAL | FunctionSymbol.RETURNOVERLOAD);
		final Sort lambdaSort = getSort(SMTLIBConstants.FUNC, generic2);
		// arrayof : (-> X Y) -> (Array X Y)
		declareInternalPolymorphicFunction(SMTLIBConstants.ARRAYOF, generic2, new Sort[] { lambdaSort }, array,
				FunctionSymbol.INTERNAL | FunctionSymbol.RETURNOVERLOAD);
	}

	private void createBitVecSort() {
		mBitVecSort = new SortSymbol(this, "BitVec", 0, null, SortSymbol.INTERNAL | SortSymbol.INDEXED) {
			@Override
			public void checkArity(final String[] indices, final int arity) {
				if (indices == null || indices.length != 1) {
					throw new IllegalArgumentException("BitVec needs one index");
				}
				if (toNumeral(indices[0]).signum() <= 0) {
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
			public int getFlags(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
				return mFlags;
			}

			@Override
			public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
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
			public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices == null || indices.length != 1 || paramSorts.length != 1 || resultSort != null
						|| paramSorts[0].getName() != "BitVec") {
					return null;
				}
				final BigInteger size = toNumeral(indices[0]).add(toNumeral(paramSorts[0].getIndices()[0]));
				return mBitVecSort.getSort(new String[] { size.toString() }, new Sort[0]);
			}
		}
		class RotateBitVecFunction extends FunctionSymbolFactory {
			public RotateBitVecFunction(final String name) {
				super(name);
			}

			@Override
			public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices == null || indices.length != 1 || paramSorts.length != 1 || resultSort != null
						|| paramSorts[0].getName() != "BitVec") {
					return null;
				}
				return paramSorts[0];
			}
		}
		class Bv2NatFunction extends FunctionSymbolFactory {
			public Bv2NatFunction(final String name) {
				super(name);
				assert name.equals("bv2nat") : "Wrong name: " + name;
			}

			@Override
			public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices != null || paramSorts.length != 1 || paramSorts[0].getName() != "BitVec"
						|| resultSort != null) {
					return null;
				}
				return mNumericSort;
			}
		}
		class Nat2BvFunction extends FunctionSymbolFactory {
			public Nat2BvFunction(final String name) {
				super(name);
				assert name.equals("nat2bv") : "Wrong name: " + name;
			}

			@Override
			public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices == null || indices.length != 1 || paramSorts.length != 1
						|| !paramSorts[0].getName().equals("Int") || resultSort != null) {
					return null;
				}
				return mBitVecSort.getSort(indices);
			}
		}
		declareInternalFunctionFactory(new FunctionSymbolFactory("concat") {
			@Override
			public int getFlags(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
				return FunctionSymbol.INTERNAL;
			}

			@Override
			public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices != null || paramSorts.length != 2 || resultSort != null
						|| paramSorts[0].getName() != "BitVec" || paramSorts[1].getName() != "BitVec") {
					return null;
				}

				final BigInteger paramSortAsInt0 = toNumeral(paramSorts[0].getIndices()[0]);
				final BigInteger paramSortAsInt1 = toNumeral(paramSorts[1].getIndices()[0]);

				final BigInteger size = paramSortAsInt0.add(paramSortAsInt1);
				// before: final BigInteger size = paramSorts[0].getIndices()[0].add(paramSorts[1].getIndices()[0]);
				return mBitVecSort.getSort(new String[] { size.toString() }, new Sort[0]);
				// what does { size } ?
			}
		});
		declareInternalFunctionFactory(new FunctionSymbolFactory("extract") {
			@Override
			public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices == null || indices.length < 2 || paramSorts.length != 1 || resultSort != null
						|| paramSorts[0].getName() != "BitVec") {
					return null;
				}
				final BigInteger idxFirst = toNumeral(indices[0]);
				final BigInteger idxScnd = toNumeral(indices[1]);
				final BigInteger paramLength = toNumeral(paramSorts[0].getIndices()[0]);
				if (idxFirst.compareTo(idxScnd) < 0 || paramLength.compareTo(idxFirst) < 0) {
					return null;
				}
				final BigInteger size = idxFirst.subtract(idxScnd).add(BigInteger.ONE);
				return mBitVecSort.getSort(new String[] { size.toString() }, new Sort[0]);
			}
		});
		final Sort bitvec1 = mBitVecSort.getSort(new String[] { BigInteger.ONE.toString() }, new Sort[0]);

		declareInternalFunctionFactory(new RegularBitVecFunction("bvnot", 1, null));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvand", 2, null, FunctionSymbol.INTERNAL | FunctionSymbol.LEFTASSOC));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvor", 2, null, FunctionSymbol.INTERNAL | FunctionSymbol.LEFTASSOC));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvneg", 1, null));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvadd", 2, null, FunctionSymbol.INTERNAL | FunctionSymbol.LEFTASSOC));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvmul", 2, null, FunctionSymbol.INTERNAL | FunctionSymbol.LEFTASSOC));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvudiv", 2, null));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvurem", 2, null));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvshl", 2, null));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvlshr", 2, null));

		declareInternalFunctionFactory(new RegularBitVecFunction("bvnand", 2, null));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvnor", 2, null));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvxor", 2, null, FunctionSymbol.INTERNAL | FunctionSymbol.LEFTASSOC));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvxnor", 2, null));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvcomp", 2, bitvec1));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvsub", 2, null));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvsdiv", 2, null));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvsrem", 2, null));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvsmod", 2, null));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvashr", 2, null));

		declareInternalFunctionFactory(new FunctionSymbolFactory("repeat") {
			@Override
			public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices == null || indices.length != 1 || paramSorts.length != 1 || resultSort != null
						|| paramSorts[0].getName() != "BitVec") {
					return null;
				}
				final BigInteger size = toNumeral(indices[0]).multiply(toNumeral(paramSorts[0].getIndices()[0]));
				return mBitVecSort.getSort(new String[] { size.toString() }, new Sort[0]);
			}
		});
		declareInternalFunctionFactory(new ExtendBitVecFunction("zero_extend"));
		declareInternalFunctionFactory(new ExtendBitVecFunction("sign_extend"));
		declareInternalFunctionFactory(new RotateBitVecFunction("rotate_left"));
		declareInternalFunctionFactory(new RotateBitVecFunction("rotate_right"));

		declareInternalFunctionFactory(new RegularBitVecFunction("bvult", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvule", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvugt", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvuge", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvslt", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvsle", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvsgt", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));
		declareInternalFunctionFactory(new RegularBitVecFunction("bvsge", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));

		declareInternalFunctionFactory(new Bv2NatFunction("bv2nat"));
		declareInternalFunctionFactory(new Nat2BvFunction("nat2bv"));



	}

	private void createFloatingPointOperators() {

		mFloatingPointSort = new SortSymbol(this, "FloatingPoint", 0, null, SortSymbol.INTERNAL | SortSymbol.INDEXED) {
			@Override
			public void checkArity(final String[] indices, final int arity) {
				if (indices == null || indices.length != 2) {
					throw new IllegalArgumentException("Floating Point needs two indices");
				}

				if (toNumeral(indices[0]).signum() <= 0 || toNumeral(indices[1]).signum() <= 0) {
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
			public int getFlags(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
				return mFlags;
			}

			@Override
			public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
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

		declareInternalFunctionFactory(new FunctionSymbolFactory("fp") {
			@Override
			public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices != null || paramSorts.length != 3 || resultSort != null
						|| paramSorts[0].getName() != "BitVec" || paramSorts[1].getName() != "BitVec"
						|| paramSorts[2].getName() != "BitVec") {
					return null;
				}
				final BigInteger fpSignIndex = toNumeral(paramSorts[0].getIndices()[0]);
				if (!fpSignIndex.equals(BigInteger.ONE)) {
					return null;
				}
				final String[] fpIndices = new String[2];
				fpIndices[0] = toNumeral(paramSorts[1].getIndices()[0]).toString();
				fpIndices[1] = toNumeral(paramSorts[2].getIndices()[0]).add(BigInteger.ONE).toString();
				return mFloatingPointSort.getSort(fpIndices, new Sort[0]);
			}
		});

		// from BitVec to FP
		declareInternalFunctionFactory(new FunctionSymbolFactory("to_fp") {
			@Override
			public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices == null || indices.length != 2 || paramSorts == null) {
					return null;
				}
				// from BitVec to FP
				if (paramSorts.length == 1 && paramSorts[0].getName() == "BitVec") {
					if (!((toNumeral(indices[0]).add(toNumeral(indices[1]))
							.equals(toNumeral(paramSorts[0].getIndices()[0]))))) {
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

		declareInternalFunctionFactory(new FunctionSymbolFactory("to_fp_unsigned") {
			@Override
			public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices == null || indices.length != 2 || paramSorts.length != 2 || resultSort != null
						|| paramSorts[0].getName() != "RoundingMode" || paramSorts[1].getName() != "BitVec") {
					return null;
				}
				return mFloatingPointSort.getSort(indices, new Sort[0]);
			}
		});

		declareInternalFunctionFactory(new FunctionSymbolFactory("fp.to_ubv") {
			@Override
			public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices == null || indices.length != 1 || paramSorts.length != 2 || resultSort != null
						|| paramSorts[0].getName() != "RoundingMode" || paramSorts[1].getName() != "FloatingPoint") {
					return null;
				}
				return mBitVecSort.getSort(new String[] { indices[0] }, new Sort[0]);
			}
		});

		declareInternalFunctionFactory(new FunctionSymbolFactory("fp.to_sbv") {
			@Override
			public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices == null || indices.length != 1 || paramSorts.length != 2 || resultSort != null
						|| paramSorts[0].getName() != "RoundingMode" || paramSorts[1].getName() != "FloatingPoint") {
					return null;
				}
				return mBitVecSort.getSort(new String[] { indices[0] }, new Sort[0]);
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
			public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices.length != 2 || paramSorts.length != 0 || resultSort != null) {
					return null;
				}
				return mFloatingPointSort.getSort(indices, new Sort[0]);
			}
		}
		// +/- infinity
		declareInternalFunctionFactory(new FloatingPointConstant("+oo"));
		declareInternalFunctionFactory(new FloatingPointConstant("-oo"));
		// +/- zero
		declareInternalFunctionFactory(new FloatingPointConstant("+zero"));
		declareInternalFunctionFactory(new FloatingPointConstant("-zero"));

		declareInternalFunctionFactory(new FloatingPointConstant("NaN"));

		// short forms of common floats
		defineSort("Float16", 0, mFloatingPointSort.getSort(new String[] { new String("5"), new String("11") }));
		defineSort("Float32", 0, mFloatingPointSort.getSort(new String[] { new String("8"), new String("24") }));
		defineSort("Float64", 0, mFloatingPointSort.getSort(new String[] { new String("11"), new String("53") }));
		defineSort("Float128", 0, mFloatingPointSort.getSort(new String[] { new String("15"), new String("113") }));

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
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.abs", 1, null, FunctionSymbol.INTERNAL));
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.neg", 1, null, FunctionSymbol.INTERNAL));
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.min", 2, null, FunctionSymbol.INTERNAL));
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.max", 2, null, FunctionSymbol.INTERNAL));
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.rem", 2, null, FunctionSymbol.INTERNAL));
		// rounded operators
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.add", 3, null, FunctionSymbol.INTERNAL));
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.sub", 3, null, FunctionSymbol.INTERNAL));
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.mul", 3, null, FunctionSymbol.INTERNAL));
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.div", 3, null, FunctionSymbol.INTERNAL));
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.fma", 4, null, FunctionSymbol.INTERNAL));
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.sqrt", 2, null, FunctionSymbol.INTERNAL));
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.roundToIntegral", 2, null, FunctionSymbol.INTERNAL));

		// Comparison Operators
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.leq", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.lt", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.geq", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.gt", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.eq", 2, mBooleanSort,
				FunctionSymbol.INTERNAL | FunctionSymbol.CHAINABLE));

		// Classification of numbers
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.isNormal", 1, mBooleanSort, FunctionSymbol.INTERNAL));
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.isSubnormal", 1, mBooleanSort, FunctionSymbol.INTERNAL));
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.isZero", 1, mBooleanSort, FunctionSymbol.INTERNAL));
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.isInfinite", 1, mBooleanSort, FunctionSymbol.INTERNAL));
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.isNaN", 1, mBooleanSort, FunctionSymbol.INTERNAL));
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.isNegative", 1, mBooleanSort, FunctionSymbol.INTERNAL));
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.isPositive", 1, mBooleanSort, FunctionSymbol.INTERNAL));

		// Conversion from FP
		declareInternalFunctionFactory(new RegularFloatingPointFunction("fp.to_real", 1, mRealSort, FunctionSymbol.INTERNAL));
	}

	private void createStringOperators() {
		final Sort str = declareInternalSort(SMTLIBConstants.STRING, 0, 0).getSort(null);
		final Sort re = declareInternalSort(SMTLIBConstants.REGLAN, 0, 0).getSort(null);
		mStringSort = str;
		final Sort[] str1 = new Sort[] { str };
		final Sort[] str2 = new Sort[] { str, str };
		final Sort[] str3 = new Sort[] { str, str, str };
		final Sort[] str_re = new Sort[] { str, re };
		final Sort[] str_re_str = new Sort[] { str, re, str };
		final Sort[] re1 = new Sort[] { re };
		final Sort[] re2 = new Sort[] { re, re };
		declareInternalFunctionFactory(new FunctionSymbolFactory(SMTLIBConstants.CHAR) {
			@Override
			public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices == null || indices.length != 1 || paramSorts.length != 0 || resultSort != null) {
					return null;
				}
				final String index = indices[0];
				if (!index.startsWith("#x") || index.length() <= 2 || index.length() > 7
						|| (index.length() == 7 && index.charAt(2) > '2')) {
					return null;
				}
				return str;
			}
		});
		declareInternalFunction(SMTLIBConstants.STR_CONCAT, str2, str, FunctionSymbol.LEFTASSOC);
		declareInternalFunction(SMTLIBConstants.STR_LT, str2, mBooleanSort, FunctionSymbol.CHAINABLE);
		declareInternalFunction(SMTLIBConstants.STR_TO_RE, str1, re, 0);
		declareInternalFunction(SMTLIBConstants.STR_IN_RE, str_re, mBooleanSort, 0);
		declareInternalFunction(SMTLIBConstants.RE_NONE, EMPTY_SORT_ARRAY, re, 0);
		declareInternalFunction(SMTLIBConstants.RE_ALL, EMPTY_SORT_ARRAY, re, 0);
		declareInternalFunction(SMTLIBConstants.RE_ALLCHAR, EMPTY_SORT_ARRAY, re, 0);
		declareInternalFunction(SMTLIBConstants.RE_CONCAT, re2, re, FunctionSymbol.LEFTASSOC);
		declareInternalFunction(SMTLIBConstants.RE_UNION, re2, re, FunctionSymbol.LEFTASSOC);
		declareInternalFunction(SMTLIBConstants.RE_INTER, re2, re, FunctionSymbol.LEFTASSOC);
		declareInternalFunction(SMTLIBConstants.RE_STAR, re1, re, 0);

		declareInternalFunction(SMTLIBConstants.STR_LE, str2, mBooleanSort, FunctionSymbol.CHAINABLE);
		declareInternalFunction(SMTLIBConstants.STR_PREFIXOF, str2, mBooleanSort, 0);
		declareInternalFunction(SMTLIBConstants.STR_SUFFIXOF, str2, mBooleanSort, 0);
		declareInternalFunction(SMTLIBConstants.STR_CONTAINS, str2, mBooleanSort, 0);
		declareInternalFunction(SMTLIBConstants.STR_REPLACE, str3, str, 0);
		declareInternalFunction(SMTLIBConstants.STR_REPLACE_ALL, str3, str, 0);
		declareInternalFunction(SMTLIBConstants.STR_REPLACE_RE, str_re_str, str, 0);
		declareInternalFunction(SMTLIBConstants.STR_REPLACE_RE_ALL, str_re_str, str, 0);

		declareInternalFunction(SMTLIBConstants.RE_COMP, re1, re, 0);
		declareInternalFunction(SMTLIBConstants.RE_DIFF, re2, re, FunctionSymbol.LEFTASSOC);
		declareInternalFunction(SMTLIBConstants.RE_PLUS, re1, re, 0);
		declareInternalFunction(SMTLIBConstants.RE_OPT, re1, re, 0);
		declareInternalFunction(SMTLIBConstants.RE_RANGE, str2, re, 0);

		declareInternalFunction(SMTLIBConstants.STR_IS_DIGIT, str1, mBooleanSort, 0);

		declareInternalFunctionFactory(new FunctionSymbolFactory(SMTLIBConstants.RE_ITER) {
			@Override
			public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices == null || indices.length != 1 || paramSorts.length != 1 || resultSort != null
						|| paramSorts[0] != re) {
					return null;
				}
				toNumeral(indices[0]);
				return re;
			}
		});
		declareInternalFunctionFactory(new FunctionSymbolFactory(SMTLIBConstants.RE_LOOP) {
			@Override
			public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
				if (indices == null || indices.length != 2 || paramSorts.length != 1 || resultSort != null
						|| paramSorts[0] != re) {
					return null;
				}
				toNumeral(indices[0]);
				toNumeral(indices[1]);
				return re;
			}
		});
		if (mLogic.hasIntegers()) {
			final Sort[] int1 = new Sort[] { mNumericSort };
			final Sort[] str_int = new Sort[] { str, mNumericSort };
			final Sort[] str2_int = new Sort[] { str, str, mNumericSort };
			final Sort[] str_int2 = new Sort[] { str, mNumericSort, mNumericSort };
			declareInternalFunction(SMTLIBConstants.STR_LEN, str1, mNumericSort, 0);
			declareInternalFunction(SMTLIBConstants.STR_AT, str_int, str, 0);
			declareInternalFunction(SMTLIBConstants.STR_SUBSTR, str_int2, str, 0);
			declareInternalFunction(SMTLIBConstants.STR_INDEXOF, str2_int, mNumericSort, 0);
			declareInternalFunction(SMTLIBConstants.STR_TO_CODE, str1, mNumericSort, 0);
			declareInternalFunction(SMTLIBConstants.STR_FROM_CODE, int1, str, 0);
			declareInternalFunction(SMTLIBConstants.STR_TO_INT, str1, mNumericSort, 0);
			declareInternalFunction(SMTLIBConstants.STR_FROM_INT, int1, str, 0);
		}
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

		if (logic.isString()) {
			createStringOperators();
		}
		if (mSolverSetup != null) {
			mSolverSetup.setLogic(this, logic);
		}
		if (logic.isDatatype()) {
			declareInternalFunctionFactory(new IsConstructorFactory());
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
	public Sort getSort(final String id, final String[] indices, final Sort... args) {
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

	public void declareInternalFunctionFactory(final FunctionSymbolFactory factory) {
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

	public Map<String, SortSymbol> getDeclaredSorts() {
		return mDeclaredSorts;
	}

	public Map<String, FunctionSymbolFactory> getFunctionFactories() {
		return mFunFactory;
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

	public FunctionSymbol getFunctionWithResult(final String name, final String[] indices, final Sort resultType,
			final Sort... paramTypes) {
		final FunctionSymbolFactory factory = mFunFactory.get(name);
		if (factory != null) {
			FunctionSymbol fsym = factory.getFunctionWithResult(this, indices, paramTypes, resultType);
			if (fsym == null && mIRAWrappers != null) {
				fsym = mIRAWrappers.createWrapper(this, name, indices, paramTypes, resultType);
			}
			if (fsym == null) {
				final StringBuilder sb = new StringBuilder();
				final PrintTerm pt = new PrintTerm();
				sb.append("Builtin function ");
				if (indices != null) {
					sb.append("(_ ").append(name);
					for (final String i : indices) {
						sb.append(" ").append(i);
					}
					sb.append(") does not support indices or argument sorts (");
				} else {
					sb.append(name);
					sb.append(" does not support argument sorts (");
				}
				String sep = "";
				for (final Sort s : paramTypes) {
					sb.append(sep);
					pt.append(sb, s);
					sep = " ";
				}
				sb.append(")");
				throw new SMTLIBException(sb.toString());
			}
			return fsym;
		}
		FunctionSymbol fsym = mDeclaredFuns.get(name);
		if (fsym != null) {
			if (indices != null) {
				throw new SMTLIBException("Function " + name + " take no index.");
			}
			if (resultType != null || !fsym.typecheck(paramTypes)) {
				if (mIRAWrappers != null) {
					fsym = mIRAWrappers.createWrapper(this, name, indices, paramTypes, resultType);
					if (fsym != null) {
						return fsym;
					}
				}
				throw new SMTLIBException(
						"Application of function " + fsym + " does not type check.");
			}
			return fsym;
		}
		if (resultType != null && indices == null && paramTypes.length == 0 && name.matches(MODEL_VALUE_PATTERN)) {
			return getModelValueSymbol(name, resultType);
		}
		if (mBitVecSort != null && name.matches(BITVEC_CONST_PATTERN) && indices != null && indices.length == 1
				&& resultType == null) {
			/* Create bitvector constants */
			return getBitVecConstant(name, indices);
		}
		throw new SMTLIBException("Unknown function symbol " + name + ".");
	}

	private FunctionSymbol getBitVecConstant(final String name, final String[] indices) {
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

	public Term term(final FunctionSymbolFactory factory, final Term... parameters) {
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

	public Term term(final String funcname, final String[] indices,
			final Sort returnSort, final Term... params) throws SMTLIBException {
		final Sort[] sorts = params.length == 0 ? Script.EMPTY_SORT_ARRAY : new Sort[params.length];
		for (int i = 0; i < sorts.length; i++) {
			sorts[i] = params[i].getSort();
		}
		final FunctionSymbol fsym = getFunctionWithResult(funcname, indices, returnSort, sorts);
		return term(fsym, params);
	}

	public Term term(final String func, final Term... parameters) {
		return term(func, null, null, parameters);
	}

	public Term term(final FunctionSymbol func, Term... parameters) {
		// Special case for normalizing rationals: we want to use ConstantValue with Rational, for things
		// like (/ 1.0 2.0), to avoid the overhead of parsing them again. To avoid two terms that look identical but are
		// not equal, we don't create an ApplicationTerm when parsing rational constants.
		if (func.isIntern() && func.getName().equals(SMTLIBConstants.DIVIDE) && parameters.length == 2
				&& parameters[0] instanceof ConstantTerm && parameters[1] instanceof ConstantTerm
				&& parameters[0].getSort() == getRealSort() && parameters[1].getSort() == getRealSort()) {
			final ConstantTerm numTerm = (ConstantTerm) parameters[0];
			final ConstantTerm denomTerm = (ConstantTerm) parameters[1];
			BigInteger num = null, denom = null;
			if (numTerm.getValue() instanceof Rational && denomTerm.getValue() instanceof Rational) {
				final Rational numRat = (Rational) numTerm.getValue();
				final Rational denomRat = (Rational) denomTerm.getValue();
				if (numRat.isIntegral() && denomRat.isIntegral()) {
					num = numRat.numerator();
					denom = denomRat.numerator();
				}
			}
			// make sure that num and denom have the right form such that the created
			// rational term would be completely identical
			if (num != null && denom.compareTo(BigInteger.ONE) > 0 && num.gcd(denom).equals(BigInteger.ONE)) {
				final Rational value = Rational.valueOf(num, denom);
				return constant(value, getRealSort());
			}
		}
		if (func.isIntern() && func.getName().equals(SMTLIBConstants.MINUS) && parameters.length == 1
				&& parameters[0] instanceof ConstantTerm
				&& (parameters[0].getSort() == getNumericSort() || parameters[0].getSort() == getRealSort())) {
			final ConstantTerm numTerm = (ConstantTerm) parameters[0];
			if (numTerm.getValue() instanceof Rational) {
				final Rational num = (Rational) numTerm.getValue();
				// make sure that num has the right form. In particular we only allow negating integrals, as the
				// normal form of -.5 is (/ (- 1.0) 2.0).
				if (num.isIntegral() && num.signum() > 0) {
					return constant(num.negate(), numTerm.getSort());
				}
			} else if (numTerm.getValue() instanceof BigInteger) {
				final BigInteger num = (BigInteger) numTerm.getValue();
				// make sure that num is positive.
				if (num.signum() > 0) {
					return constant(num.negate(), numTerm.getSort());
				}
			}
		}

		// Not a rational term to normalize
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

	public DataType.Constructor createConstructor(final String name, final String[] selectors,
			final Sort[] argumentSorts) {
		final DataType.Constructor constructor = new DataType.Constructor(name, selectors, argumentSorts);
		return constructor;

	}

	/**
	 * Create a new data type with the given name and number of parameters.
	 *
	 * @param name
	 *            the variable name.
	 * @param numParams
	 *            the number of parameters of the data type.
	 * @return a data type.
	 */
	public DataType createDatatypes(final String name, final int numParams) {
		if (mDeclaredSorts.containsKey(name)) {
			throw new SMTLIBException("Datatype " + name + " already exists.");
		}
		final DataType datatype = new DataType(this, name, numParams);
		mDeclaredSorts.put(name, datatype);
		return datatype;
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
			mFunFactory.beginScope();
			mDeclaredFuns.beginScope();
			mDeclaredSorts.beginScope();
		}
	}

	public void pop() {
		if (!mGlobalDecls) {
			mFunFactory.endScope();
			mDeclaredFuns.endScope();
			mDeclaredSorts.endScope();
		}
	}

	/**
	 * Create a fresh auxiliary function that stands for the given term and takes the given variables as arguments.
	 */
	public FunctionSymbol createFreshAuxFunction(final TermVariable[] vars, final Term term) {
		final Sort[] paramSorts = new Sort[vars.length];
		for (int i = 0; i < vars.length; i++) {
			paramSorts[i] = vars[i].getSort();
		}
		return declareInternalFunction("@AUX" + (mAuxCounter++), paramSorts, vars, term,
				FunctionSymbol.UNINTERPRETEDINTERNAL); // TODO Change flag?
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
		while (mFunFactory.getActiveScopeNum() > 1) {
			mFunFactory.endScope();
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
