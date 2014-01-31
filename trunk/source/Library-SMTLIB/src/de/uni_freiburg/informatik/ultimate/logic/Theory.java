/*
 * Copyright (C) 2009-2012 University of Freiburg
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
import java.util.LinkedHashSet;

import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;
import de.uni_freiburg.informatik.ultimate.util.UnifyHash;


/**
 * The theory is not intended for public use.  Please stick to the
 * {@link Script} interface and use the functions in {@link Util} to simplify
 * logical formulas.
 * 
 * The theory is a container for the function symbols, sort symbols and a
 * unifier for all terms created by this theory.  Each sort belongs to one
 * theory and since every function symbol and every term has a sort, they also
 * belong to one theory.
 * 
 * The theory also defines all predefined function symbols required by the 
 * logic that was set with setLogic().  It allows creating new function and
 * sort symbols.
 * 
 * @author Jochen Hoenicke
 */
public class Theory {
	
	/**
	 * Helper class to set up symbols specific to a solver.
	 * @author Juergen Christ
	 */
	public static abstract class SolverSetup {
		/**
		 * Set up symbols needed by this solver.  These symbols might depend
		 * upon the logic, e.g., the diff-symbol needed for quantifier-free
		 * array interpolation. 
		 * @param theory The theory to be used by the solver.
		 * @param logic  The logic set for this theory 
		 *        (@see {@link Theory#getLogic()}).
		 */
		public abstract void setLogic(Theory theory, Logics logic);
		/// *** Delegators ***
		protected final void declareInternalSort(
				Theory theory, String name, int cardinality, int flags) {
			theory.declareInternalSort(name, cardinality, flags);
		}
		protected final void declareInternalFunction(Theory theory, String name,
				Sort[] paramSorts, Sort resultSort, int flags) {
			theory.declareInternalFunction(name, paramSorts, resultSort, flags);
		}
		protected final void declareInternalFunction(Theory theory, String name,
				Sort[] paramTypes, TermVariable[] defVars, Term definition,
				int flags) {
			theory.declareInternalFunction(
					name, paramTypes, defVars, definition, flags);
		}

		protected final void declareInternalPolymorphicFunction(Theory theory,
				String name, Sort[] sortParams,
				Sort[] paramTypes, Sort resultType, int flags) {
			theory.declareInternalPolymorphicFunction(
					name, sortParams, paramTypes, resultType, flags);
		}
		
		protected final void defineFunction(
				Theory theory, FunctionSymbolFactory factory) {
			theory.defineFunction(factory);
		}
	}
	
	private SolverSetup mSolverSetup;
	private Logics mLogic;
	private boolean mIsUFLogic;
	private Sort mNumericSort, mRealSort, mStringSort, mBooleanSort;
	private SortSymbol mBitVecSort;
	private final HashMap<String, FunctionSymbolFactory> mFunFactory = 
		new HashMap<String, FunctionSymbolFactory>();

	private final ScopedHashMap<String, SortSymbol> mDeclaredSorts = 
		new ScopedHashMap<String, SortSymbol>();
	private final ScopedHashMap<String, FunctionSymbol> mDeclaredFuns = 
		new ScopedHashMap<String, FunctionSymbol>();
	
	private final UnifyHash<QuantifiedFormula> mQfCache =
			new UnifyHash<QuantifiedFormula>();
	private final UnifyHash<LetTerm> mLetCache = new UnifyHash<LetTerm>();
	private final UnifyHash<Term> mTermCache = new UnifyHash<Term>();
	private final UnifyHash<TermVariable> mTvUnify =
			new UnifyHash<TermVariable>();
	
	public final ApplicationTerm mTrue, mFalse;
	public final FunctionSymbol mAnd, mOr, mNot, mImplies, mXor;
	public final PolymorphicFunctionSymbol mEquals, mDistinct, mIte;
	
	private final static Sort[] EMPTY_SORT_ARRAY = {};
	
	private int mTvarCtr = 0;
	
	private int mSkolemCounter = 0;
	
	public Theory() {
		mIsUFLogic = false;
		mTrue = mFalse = null;
		mAnd = mOr = mNot = mImplies = mXor = null;
		mEquals = mDistinct = mIte = null;
	}
	
	public Theory(Logics logic) {
		this(logic, null);
	}
	
	/**
	 * Create the term factory.  The solver setup should be used to create
	 * internal function symbols, e.g., to represent proof objects.
	 * @param logic       The logic to use.
	 * @param solverSetup The solver-specific setup delegate.
	 */
	public Theory(Logics logic, SolverSetup solverSetup) {
		mSolverSetup = solverSetup;
		Sort[] noarg = new Sort[0];
		mBooleanSort = declareInternalSort("Bool", 0, 0).getSort(
				null, noarg);
		Sort[] generic1 = createSortVariables("A");
		Sort[] bool1 = new Sort[] { mBooleanSort};
		Sort[] bool2 = new Sort[] { mBooleanSort, mBooleanSort};
		Sort[] generic2 = new Sort[] { generic1[0], generic1[0] };
		int leftassoc = FunctionSymbol.LEFTASSOC;
		mNot = declareInternalFunction("not", bool1, mBooleanSort, 0);
		mAnd = declareInternalFunction("and", bool2, mBooleanSort, leftassoc);
		mOr  = declareInternalFunction("or",  bool2, mBooleanSort, leftassoc); 
		mImplies = declareInternalFunction(
				"=>",  bool2, mBooleanSort, FunctionSymbol.RIGHTASSOC);
		mEquals = declareInternalPolymorphicFunction("=", generic1, generic2,
				mBooleanSort, FunctionSymbol.CHAINABLE);
		mDistinct = declareInternalPolymorphicFunction(
				"distinct", generic1, generic2,
				mBooleanSort, FunctionSymbol.PAIRWISE);
		mXor = declareInternalFunction("xor", bool2, mBooleanSort, leftassoc);
		mIte = declareInternalPolymorphicFunction(
				"ite", generic1,
				new Sort[] { mBooleanSort, generic1[0], generic1[0] },
				generic1[0], 
				0);
		mTrue  = term(declareInternalFunction("true", noarg, mBooleanSort, 0)); 
		mFalse = term(declareInternalFunction("false", noarg, mBooleanSort, 0));
		// Finally, declare logic specific functions
		setLogic(logic);
	}

	/******************** LOGICAL OPERATORS *******************************/
	
	private Term simplifyAndOr(FunctionSymbol connector, Term... subforms) {
		Term neutral = (connector == mAnd ? mTrue : mFalse);
		LinkedHashSet<Term> formulas = new LinkedHashSet<Term>();
		
		for (Term f : subforms) {
			if (f == mTrue || f == mFalse) {
				if (f == neutral)
					continue;
				else
					return f;
			}

			/* Normalize nested and/ors */
			if (f instanceof ApplicationTerm
				&& ((ApplicationTerm) f).getFunction() == connector) {
				for (Term subf : ((ApplicationTerm) f).getParameters())
					formulas.add(subf);
			} else
				formulas.add(f);
		}
		if (formulas.size() <= 1) {
			if (formulas.isEmpty())
				return neutral;
			else
				return formulas.iterator().next();
		}
		Term[] arrforms = formulas.toArray(new Term[formulas.size()]);
		return term(connector, arrforms);
	}

	public Term not(Term f) {
		if (f == mTrue) return mFalse;
		if (f == mFalse) return mTrue;
		if (f instanceof ApplicationTerm
			&& ((ApplicationTerm)f).getFunction() == mNot)
			return ((ApplicationTerm) f).getParameters()[0];
		return term(mNot, f);
	}

	public Term and(Term... subforms) {
		return simplifyAndOr(mAnd, subforms);
	}
	public Term or(Term... subforms) {
		return simplifyAndOr(mOr, subforms);
	}

	public Term implies(Term f, Term g) { 
		if (g == mTrue || f == mTrue) return g;
		if (f == mFalse) return mTrue;
		if (g == mFalse) return not(f);
		if (f == g) return mTrue;
		return term(mImplies, f, g);
	}

	public Term xor(Term f, Term g)	{ 
		if (f == mTrue) return not(g);
		if (g == mTrue) return not(f);
		if (f == mFalse) return g;
		if (g == mFalse) return f;
		if (f == g) return mFalse;
		return term(mXor, f, g);
	}

	public Term ifthenelse(Term c, Term t, Term e) {
		if (c == mTrue)  return t;
		if (c == mFalse) return e;
		if (t == e) return t;
		if (t == mTrue && e == mFalse)
			return c;
		if (t == mFalse && e == mTrue)
			return not(c);
		if (t == mTrue)
			return term(mOr, c, e);
		if (t == mFalse)
			return term(mAnd, term(mNot, c), e);
		if (e == mTrue)
			return term(mImplies, c, t);
		if (e == mFalse)
			return term(mAnd, c, t);
		return term(mIte, c, t, e);
	}

	private Term quantify(int quant, TermVariable[] vars, Term f) {
		if (f == mTrue || f == mFalse)
			return f;
		int hash = QuantifiedFormula.hashQuantifier(quant, vars, f);
		for (QuantifiedFormula qf : mQfCache.iterateHashCode(hash)) {
			if (qf.getQuantifier() == quant && qf.getSubformula() == f 
				&& Arrays.equals(vars,qf.getVariables()))
				return qf;
		}
		QuantifiedFormula qf = 
			new QuantifiedFormula(quant, vars, f, hash);
		mQfCache.put(hash,qf);
		return qf;
	}
	public Term exists(TermVariable[] vars, Term f)	{
		return quantify(QuantifiedFormula.EXISTS, vars, f);
	}
	public Term forall(TermVariable[] vars, Term f)	{
		return quantify(QuantifiedFormula.FORALL, vars, f);
	}
	
	public Term let(TermVariable[] vars, Term[] values, Term subform) {
		assert (vars.length == values.length);
		if (vars.length == 0)
			return subform;
		int hash = LetTerm.hashLet(vars, values, subform);
		for (LetTerm lt : mLetCache.iterateHashCode(hash)) {
			if (lt.getSubTerm() == subform
				&& Arrays.equals(lt.getVariables(), vars)
				&& Arrays.equals(lt.getValues(), values))
				return lt;
		}
		LetTerm lf = new LetTerm(vars, values, subform, hash);
		mLetCache.put(hash,lf);
		return lf;
	}

	public Term let(TermVariable var, Term value, Term subform) {
		return let(new TermVariable[] {var}, new Term[]{value}, subform);
	}

	public Term distinct(Term... terms)	{
		if (terms.length < 2)
			return null;
		if (terms.length == 2) {
			if (terms[0] == terms[1])
				return mFalse;
			if (terms[0].getSort() == mBooleanSort) {
				if (terms[0] == mFalse) return terms[1];
				if (terms[1] == mFalse) return terms[0];
				if (terms[0] == mTrue) return not(terms[1]);
				if (terms[1] == mTrue) return not(terms[0]);
			}
			return term(mDistinct, terms);
		}
		HashSet<Term> params = new HashSet<Term>(Arrays.asList(terms));
		if (params.size() != terms.length)
			// We had something like (distinct ... a ... a ...)
			return mFalse;
		return term(mDistinct, terms);
	}
	public Term equals(Term... terms) {
		if (terms.length < 2)
			return null;
		if (terms.length == 2) {
			if (terms[0] == terms[1])
				return mTrue;
			if (terms[0].getSort() == mBooleanSort) {
				if (terms[0] == mTrue) return terms[1];
				if (terms[1] == mTrue) return terms[0];
				if (terms[0] == mFalse) return not(terms[1]);
				if (terms[1] == mFalse) return not(terms[0]);
			}
			return term(mEquals, terms);
		}
		HashSet<Term> params = new HashSet<Term>(Arrays.asList(terms));
		if (params.size() == 1)
			// We had (= a a ... a)
			return mTrue;
		return term(mEquals, terms);
	}

	/******************** CONSTANTS *************************************/

	public Term constant(Object value, Sort sort) {
		if (value instanceof Rational) {
			if (!sort.isNumericSort())
				throw new SMTLIBException("Not a numeric sort");
			Rational v = (Rational) value;
			if (!v.isRational())
				throw new SMTLIBException("Infinite/NaN value");
			if (sort.getName().equals("Int") && !v.isIntegral())
				throw new SMTLIBException(
						"Non-integral value with integer sort");
		}
		int hash = ConstantTerm.hashConstant(value, sort);
		for (Term t : mTermCache.iterateHashCode(hash)) {
			if (t instanceof ConstantTerm) {
				ConstantTerm nt = (ConstantTerm)t;
				if (nt.getSort() == sort && value.equals(nt.getValue()))
					return  nt;
			}
		}
		ConstantTerm nt = new ConstantTerm(value, sort, hash);
		mTermCache.put(hash,nt);
		return nt;
	}
	
	public Term numeral(BigInteger num) {
		Term result = constant(num.abs(), mNumericSort);
		if (num.signum() < 0) {
			FunctionSymbol neg = getFunction("-", mNumericSort);
			result = term(neg, result);
		}
		return result;
	}
	public Term numeral(String num) {
		return numeral(new BigInteger(num));
	}

	public Term decimal(BigDecimal value) {
		// Fix for 1 vs 1.0: Normalize to .0 for constants.
		if (value.scale() == 0)
			value = value.setScale(1);
		Term result = constant(value.abs(), mRealSort);
		if (value.signum() < 0) {
			FunctionSymbol neg = getFunction("-", mRealSort);
			result = term(neg, result);
		}
		return result;
	}
	public Term decimal(String value) {
		return decimal(new BigDecimal(value));
	}

	/**
	 * Convert a rational constant to a term of the correct sort.
	 * The constant must be integral if the sort is integer.
	 * @param c the constant to convert.
	 * @param sort the sort; either Real or Int.
	 * @return an smt term representing constant c.
	 */
	public Term rational(Rational c, Sort sort) {
		// This must not be an infinite or a NAN.
		assert c.denominator().signum() == 1;
		if (sort == mRealSort) {
			return rational(c.numerator(), c.denominator());
		} else {
			assert c.isIntegral();
			return numeral(c.numerator());
		}
	}

	public Term binary(String value) {
		assert value.startsWith("#b");
		if (mBitVecSort == null)
			return null;
		BigInteger bsize = BigInteger.valueOf(value.length() - 2);
		Sort sort = mBitVecSort.getSort(
				new BigInteger[] { bsize }, new Sort[0]);
		return new ConstantTerm(value, sort,
				ConstantTerm.hashConstant(value, sort));
	}
	
	public Term hexadecimal(String value) {
		assert value.startsWith("#x");
		if (mBitVecSort == null)
			return null;
		BigInteger bsize = BigInteger.valueOf(4 * (value.length() - 2));// NOCHECKSTYLE
		Sort sort = mBitVecSort.getSort(
				new BigInteger[] { bsize }, new Sort[0]);
		return new ConstantTerm(value, sort,
				ConstantTerm.hashConstant(value, sort));
	}
	
	public Term rational(BigInteger num, BigInteger denom) {
		BigInteger gcd = num.gcd(denom);
		if (denom.signum() * gcd.signum() < 0)
			gcd = gcd.negate();
		num = num.divide(gcd);
		denom = denom.divide(gcd);
		
		if (denom.equals(BigInteger.ONE))
			return decimal(new BigDecimal(num));// numeral(num);
		FunctionSymbol div = getFunction("/", mNumericSort, mNumericSort);
		return term(div, numeral(num), numeral(denom));
	}
	
	public Term modelRational(Rational rat, Sort sort) {
		if (sort == mRealSort) {
			BigInteger num = rat.numerator();
			BigInteger denom = rat.denominator();
			
			if (denom.equals(BigInteger.ONE) && !mLogic.isIRA()) {
				return decimal(new BigDecimal(num));
			} else {
				if (mLogic.isIRA()) {
					FunctionSymbol div = getFunction("/", mRealSort, mRealSort);
					FunctionSymbol toreal = getFunction("to_real", mNumericSort);
					Term numeralTerm = term(toreal, numeral(num.abs()));
					if (num.signum() < 0)
						numeralTerm = term("-", numeralTerm);
					return term(div, numeralTerm, term(toreal, numeral(denom)));
				} else  {
					FunctionSymbol div =
							getFunction("/", mNumericSort, mNumericSort);
					return term(div, numeral(num), numeral(denom));
				}
			}
		} else {
			assert rat.isIntegral();
			return numeral(rat.numerator());
		}
	}
	
	public Term string(String value) {
		return constant(new QuotedObject(value), mStringSort);
	}

	/******************** LOGICS AND THEORIES ********************************/
	public Logics getLogic() {
		return mLogic;
	}

	FunctionSymbol declareInternalFunction(String name, Sort[] paramTypes, 
			Sort resultType, int flags) {
		return defineFunction(name, paramTypes, resultType, null, null, 
			flags | FunctionSymbol.INTERNAL);
	}

	FunctionSymbol declareInternalFunction(String name, Sort[] paramTypes, 
			TermVariable[] defVars, Term definition, int flags) {
		return defineFunction(name, paramTypes, definition.getSort(), 
				defVars, definition, flags | FunctionSymbol.INTERNAL);
	}

	PolymorphicFunctionSymbol declareInternalPolymorphicFunction(
			String name, Sort[] sortParams,
			Sort[] paramTypes, Sort resultType, int flags) {
		assert !mFunFactory.containsKey(name);
		PolymorphicFunctionSymbol f = new PolymorphicFunctionSymbol(
				name, sortParams, paramTypes, resultType,
				flags | FunctionSymbol.INTERNAL);
		defineFunction(f);
		return f;
	}
	
	class MinusFunctionFactory extends FunctionSymbolFactory {
		Sort mSort1, mSort2;
		public MinusFunctionFactory(Sort sort1, Sort sort2) {
			super("-");
			mSort1 = sort1;
			mSort2 = sort2;
		}

		public int getFlags(
				BigInteger[] indices, Sort[] paramSorts, Sort resultSort) {
			return paramSorts.length == 1 ?  FunctionSymbol.INTERNAL
					: FunctionSymbol.LEFTASSOC | FunctionSymbol.INTERNAL;
		}

		@Override
		public Sort getResultSort(BigInteger[] indices, Sort[] paramSorts,
				Sort resultSort) {
			if (indices != null 
				|| paramSorts.length == 0 || paramSorts.length > 2	
				|| resultSort != null
				|| (paramSorts[0] != mSort1 && paramSorts[0] != mSort2))
				return null;

			if (paramSorts.length == 2 && paramSorts[0] != paramSorts[1])
				return null;
			
			return paramSorts[0];
		}
	}
	class DivisibleFunctionFactory extends FunctionSymbolFactory {
		public DivisibleFunctionFactory() {
			super("divisible");
		}

		public Sort getResultSort(
				BigInteger[] indices, Sort[] paramSorts, Sort resultSort) {
			return indices != null && indices.length == 1
					&& indices[0].signum() > 0
					&& paramSorts.length == 1 && paramSorts[0] == mNumericSort
					&& resultSort == null ? mBooleanSort : null;
		}
	}
	private void createNumericOperators(final Sort sort, boolean isRational) {
		Sort[] sort1 = new Sort[] { sort };
		Sort[] sort2 = new Sort[] { sort, sort };
		declareInternalFunction("+", sort2, sort, FunctionSymbol.LEFTASSOC);
		defineFunction(new MinusFunctionFactory(sort, sort));
		declareInternalFunction("*", sort2, sort, FunctionSymbol.LEFTASSOC);
		if (isRational) {
			declareInternalFunction("/", sort2, sort, FunctionSymbol.LEFTASSOC);
		} else {
			declareInternalFunction(
					"div", sort2, sort, FunctionSymbol.LEFTASSOC);
			declareInternalFunction("mod", sort2, sort, 0);
			defineFunction(new DivisibleFunctionFactory());
		}
		Sort sBool = mBooleanSort;
		declareInternalFunction(">",  sort2, sBool, FunctionSymbol.CHAINABLE);
		declareInternalFunction(">=", sort2, sBool, FunctionSymbol.CHAINABLE);
		declareInternalFunction("<",  sort2, sBool, FunctionSymbol.CHAINABLE);
		declareInternalFunction("<=", sort2, sBool, FunctionSymbol.CHAINABLE);

		TermVariable x = createTermVariable("x1", sort);
		Term zero = isRational ? decimal("0.0") : numeral("0");
		Term absx = term("ite", term(">=", x, zero), x, term("-", x));
		declareInternalFunction("abs", sort1,  
				new TermVariable[]{ x }, absx, 0);
	}
	
	private void createIRAOperators() {
		class BinArithFactory extends FunctionSymbolFactory {
			Sort mReturnSort;
			int mFlags;
			BinArithFactory(String name, Sort returnSort, int flags) {
				super(name);
				mReturnSort = returnSort;
				mFlags = flags | FunctionSymbol.INTERNAL;
			}

			public int getFlags(
					BigInteger[] indices, Sort[] paramSorts, Sort resultSort) {
				return mFlags;
			}

			public Sort getResultSort(
					BigInteger[] indices, Sort[] paramSorts, Sort resultSort) {
				if (indices == null
					&& paramSorts.length == 2
					&& paramSorts[0] == paramSorts[1]
					&& (paramSorts[0] == mNumericSort
						|| paramSorts[0] == mRealSort)
					&& resultSort == null) {
					return mReturnSort == null ? paramSorts[0] : mReturnSort;
				} else
					return null;
			}
		}
		
		defineFunction(
				new BinArithFactory("+", null, FunctionSymbol.LEFTASSOC));
		defineFunction(
				new MinusFunctionFactory(mNumericSort, mRealSort));
		defineFunction(
				new BinArithFactory("*", null, FunctionSymbol.LEFTASSOC));
		defineFunction(
				new BinArithFactory(
						">", mBooleanSort, FunctionSymbol.CHAINABLE));
		defineFunction(
				new BinArithFactory(
						">=", mBooleanSort, FunctionSymbol.CHAINABLE));
		defineFunction(
				new BinArithFactory(
						"<", mBooleanSort, FunctionSymbol.CHAINABLE));
		defineFunction(
				new BinArithFactory(
						"<=", mBooleanSort, FunctionSymbol.CHAINABLE));

		Sort[] int1  = new Sort[] { mNumericSort };
		Sort[] int2  = new Sort[] { mNumericSort, mNumericSort };
		Sort[] real1 = new Sort[] { mRealSort };
		Sort[] real2 = new Sort[] { mRealSort, mRealSort };
		declareInternalFunction(
				"/", real2, mRealSort, FunctionSymbol.LEFTASSOC);
		declareInternalFunction(
				"div", int2, mNumericSort, FunctionSymbol.LEFTASSOC);
		defineFunction(new DivisibleFunctionFactory());
		declareInternalFunction("to_real", int1, mRealSort, 0);
		declareInternalFunction("to_int", real1, mNumericSort, 0);

		declareInternalFunction("mod", int2, mNumericSort, 0);
		TermVariable xr = createTermVariable("x1", mRealSort);
		// isint x: (= x (to_real (to_int x)))
		Term isintx = term("=", xr, term("to_real", term("to_int", xr)));
		declareInternalFunction("is_int", real1, 
				new TermVariable[]{ xr }, isintx, 0);

		defineFunction(new FunctionSymbolFactory("abs") {
			public Term getDefinition(TermVariable[] tvs, Sort resultSort) {
				Term zero = (resultSort == mNumericSort) ? numeral("0")
							: decimal("0.0");
				// abs x: (ite (>= x 0) x (- x))
				return term("ite", term(">=", tvs[0], zero), 
							tvs[0], term("-", tvs[0]));
			}

			public Sort getResultSort(
					BigInteger[] indices, Sort[] paramSorts, Sort resultSort) {
				if (indices == null
					&& paramSorts.length == 1
					&& (paramSorts[0] == mNumericSort
						|| paramSorts[0] == mRealSort)
					&& resultSort == null) {
					return paramSorts[0];
				} else {
					return null;
				}
			}
		});
		
	}
	
	private void createArrayOperators() {
		Sort[] generic2 = createSortVariables("X", "Y");
		SortSymbol arraySort =
				declareInternalSort("Array", 2, SortSymbol.ARRAY);
		Sort array = arraySort.getSort(null, generic2);
		declareInternalPolymorphicFunction(
				"select", generic2, new Sort[] { array, generic2[0] }, 
				generic2[1], 0);
		declareInternalPolymorphicFunction(
				"store", generic2,
				new Sort[] { array, generic2[0], generic2[1] },	array, 0);
	}
	
	private void createBitVecOperators() {
		mBitVecSort = new SortSymbol(this, "BitVec", 0, null,
				SortSymbol.INTERNAL | SortSymbol.INDEXED) {
			public void checkArity(BigInteger[] indices, int arity) {
				if (indices == null || indices.length != 1)
					throw new IllegalArgumentException(
							"BitVec needs one index");
				if (indices[0].signum() <= 0)
					throw new IllegalArgumentException(
							"BitVec index must be positive");
				if (arity != 0)
					throw new IllegalArgumentException(
							"BitVec has no parameters");
			}
		};
		mDeclaredSorts.put("BitVec", mBitVecSort);
		class RegularBitVecFunction extends FunctionSymbolFactory {
			int mNumArgs;
			Sort mResult;
			public RegularBitVecFunction(
					String name, int numArgs, Sort result) {
				super(name);
				mNumArgs = numArgs;
				mResult = result;
			}
			@Override
			public Sort getResultSort(BigInteger[] indices, Sort[] paramSorts,
					Sort resultSort) {
				if (indices != null
					|| paramSorts.length != mNumArgs || resultSort != null
					|| paramSorts[0].getName() != "BitVec")
					return null;
				for (int i = 1; i < mNumArgs; i++)
					if (paramSorts[i] != paramSorts[0])
						return null;
				return mResult == null ? paramSorts[0] : mResult;
			}
		}
		class ExtendBitVecFunction extends FunctionSymbolFactory {
			public ExtendBitVecFunction(String name) {
				super(name);
			}
			@Override
			public Sort getResultSort(BigInteger[] indices, Sort[] paramSorts,
					Sort resultSort) {
				if (indices == null || indices.length != 1
					|| paramSorts.length != 1 || resultSort != null
					|| paramSorts[0].getName() != "BitVec")
					return null;
				BigInteger size = indices[0].add(paramSorts[0].getIndices()[0]);
				return mBitVecSort.getSort(
						new BigInteger[] { size }, new Sort[0]);
			}
		}
		class RotateBitVecFunction extends FunctionSymbolFactory {
			public RotateBitVecFunction(String name) {
				super(name);
			}
			@Override
			public Sort getResultSort(BigInteger[] indices, Sort[] paramSorts,
					Sort resultSort) {
				if (indices == null || indices.length != 1
					|| paramSorts.length != 1 || resultSort != null
					|| paramSorts[0].getName() != "BitVec")
					return null;
				return paramSorts[0];
			}
		}
		defineFunction(new FunctionSymbolFactory("concat") {
			@Override
			public Sort getResultSort(BigInteger[] indices, Sort[] paramSorts,
					Sort resultSort) {
				if (indices != null
					|| paramSorts.length != 2 || resultSort != null
					|| paramSorts[0].getName() != "BitVec"
					|| paramSorts[1].getName() != "BitVec")
					return null;
				BigInteger size = paramSorts[0].getIndices()[0].
					add(paramSorts[1].getIndices()[0]);
				return mBitVecSort.getSort(
						new BigInteger[] { size }, new Sort[0]);
			}
		});
		defineFunction(new FunctionSymbolFactory("extract") {
			@Override
			public Sort getResultSort(BigInteger[] indices, Sort[] paramSorts,
					Sort resultSort) {
				if (indices == null || indices.length < 2
					|| paramSorts.length != 1 || resultSort != null
					|| paramSorts[0].getName() != "BitVec")
					return null;
				if (indices[0].compareTo(indices[1]) < 0 
					|| paramSorts[0].getIndices()[0].compareTo(indices[0]) < 0)
					return null;
				BigInteger size = indices[0].subtract(indices[1]).
					add(BigInteger.ONE);
				return mBitVecSort.getSort(
						new BigInteger[] { size }, new Sort[0]);
			}
		});
		Sort bitvec1 = mBitVecSort.
			getSort(new BigInteger[] {BigInteger.ONE}, new Sort[0]);
		
		defineFunction(new RegularBitVecFunction("bvnot", 1, null));
		defineFunction(new RegularBitVecFunction("bvand", 2, null));
		defineFunction(new RegularBitVecFunction("bvor",  2, null));
		defineFunction(new RegularBitVecFunction("bvneg", 1, null));
		defineFunction(new RegularBitVecFunction("bvadd", 2, null));
		defineFunction(new RegularBitVecFunction("bvmul", 2, null));
		defineFunction(new RegularBitVecFunction("bvudiv", 2, null));
		defineFunction(new RegularBitVecFunction("bvurem", 2, null));
		defineFunction(new RegularBitVecFunction("bvshl", 2, null));
		defineFunction(new RegularBitVecFunction("bvlshr", 2, null));
		
		defineFunction(new RegularBitVecFunction("bvnand", 2, null));
		defineFunction(new RegularBitVecFunction("bvnor", 2, null));
		defineFunction(new RegularBitVecFunction("bvxor", 2, null));
		defineFunction(new RegularBitVecFunction("bvxnor", 2, null));
		defineFunction(new RegularBitVecFunction("bvcomp", 2, bitvec1));
		defineFunction(new RegularBitVecFunction("bvsub", 2, null));
		defineFunction(new RegularBitVecFunction("bvsdiv", 2, null));
		defineFunction(new RegularBitVecFunction("bvsrem", 2, null));
		defineFunction(new RegularBitVecFunction("bvsmod", 2, null));
		defineFunction(new RegularBitVecFunction("bvashr", 2, null));
		
		defineFunction(new FunctionSymbolFactory("repeat") {
			@Override
			public Sort getResultSort(BigInteger[] indices, Sort[] paramSorts,
					Sort resultSort) {
				if (indices == null || indices.length != 1
					|| paramSorts.length != 1 || resultSort != null
					|| paramSorts[0].getName() != "BitVec")
					return null;
				BigInteger size = 
						indices[0].multiply(paramSorts[0].getIndices()[0]);
				return mBitVecSort.getSort(
						new BigInteger[] { size }, new Sort[0]);
			}
		});
		defineFunction(new ExtendBitVecFunction("zero_extend"));
		defineFunction(new ExtendBitVecFunction("sign_extend"));
		defineFunction(new RotateBitVecFunction("rotate_left"));
		defineFunction(new RotateBitVecFunction("rotate_right"));
		
		defineFunction(new RegularBitVecFunction("bvult", 2, mBooleanSort));
		defineFunction(new RegularBitVecFunction("bvule", 2, mBooleanSort));
		defineFunction(new RegularBitVecFunction("bvugt", 2, mBooleanSort));
		defineFunction(new RegularBitVecFunction("bvuge", 2, mBooleanSort));
		defineFunction(new RegularBitVecFunction("bvslt", 2, mBooleanSort));
		defineFunction(new RegularBitVecFunction("bvsle", 2, mBooleanSort));
		defineFunction(new RegularBitVecFunction("bvsgt", 2, mBooleanSort));
		defineFunction(new RegularBitVecFunction("bvsge", 2, mBooleanSort));
	}
	
	private void setLogic(Logics logic) {
		this.mLogic = logic;
		switch (logic) {
		case CORE:
			break;
		case QF_AX:
			createArrayOperators();
			break;
		case AUFLIA:
		case QF_AUFLIA:
			createArrayOperators();// fallthrough
		case UFNIA:
		case QF_UFLIA:
		case QF_UFIDL:
			mIsUFLogic = true;// fallthrough
		case QF_NIA:
		case QF_IDL:
		case QF_LIA:
			mNumericSort = declareInternalSort(
					"Int", 0, SortSymbol.NUMERIC).getSort(null, new Sort[0]);
			createNumericOperators(mNumericSort, false);
			break;
		case UFLRA:
		case QF_UFLRA:
		case QF_UFNRA:
			mIsUFLogic = true;// fallthrough
		case LRA:
		case QF_NRA:
		case QF_LRA:
		case QF_RDL:
			mRealSort = mNumericSort = 
					declareInternalSort("Real", 0, SortSymbol.NUMERIC).getSort(
						null, new Sort[0]);
			createNumericOperators(mRealSort, true);
			break;
		case QF_UF:
			mIsUFLogic = true;
			break;
		case AUFLIRA:
		case AUFNIRA:
			createArrayOperators();// fallthrough
		case QF_UFLIRA:
			mIsUFLogic = true;
			mRealSort = declareInternalSort(
					"Real", 0, SortSymbol.NUMERIC).getSort(null, new Sort[0]);
			mNumericSort = declareInternalSort(
					"Int", 0, SortSymbol.NUMERIC).getSort(null, new Sort[0]);
			createIRAOperators();
			break;
		case QF_AUFBV:
			createArrayOperators();// fallthrough
		case QF_UFBV:
			mIsUFLogic = true;// fallthrough
		case QF_BV:
			createBitVecOperators();
			break;
		case QF_ABV:
			createArrayOperators();
			createBitVecOperators();
			break;
		default:
			throw new InternalError("Don't know how to setup logic " + logic);
		}
		if (mSolverSetup != null)
			mSolverSetup.setLogic(this, logic);
	}
	
	/******************** SORTS ********************************************/
	
	private SortSymbol defineSort(String name, int paramCount, Sort definition, 
				  int flags) {
		if (!mIsUFLogic && mLogic != Logics.QF_AX 
				&& (flags & FunctionSymbol.INTERNAL) == 0)
			throw new IllegalArgumentException("Not allowed in this logic");
		SortSymbol sortsym = mDeclaredSorts.get(name);
		if (sortsym != null)
			throw new IllegalArgumentException(
					"Sort " + name + " already exists.");
		sortsym = new SortSymbol(this, name, paramCount, definition, flags); 
		mDeclaredSorts.put(name, sortsym);
		return sortsym;
	}

	public SortSymbol declareSort(String name, int paramCount) {
		return defineSort(name, paramCount, null, 0);
	}
	
	public SortSymbol defineSort(String name, int paramCount, Sort definition) {
		return defineSort(name, paramCount, definition, 0);
	}

	public Sort[] createSortVariables(String... names) {
		Sort[] sorts = new Sort[names.length];
		for (int i = 0; i < names.length; i++) {
			sorts[i] = new SortSymbol(
					this, names[i], i, null, SortSymbol.TYPEPARAM).
				getSort(null, new Sort[0]);
		}
		return sorts;
	}
	
	SortSymbol declareInternalSort(String name, int paramCount, int flags) {
		return defineSort(name, paramCount, null, flags | SortSymbol.INTERNAL);
	}

	/**
	 * Returns the sort object for a previously declared or defined sort
	 * with sort arguments.
	 * @param id The name of the sort.
	 * @param args The sort arguments.
	 * @return the sort object.
	 */
	public Sort getSort(String id, Sort... args) {
		return getSort(id, null, args);
	}

	/**
	 * Returns the sort object for a previously declared or defined sort
	 * with sort arguments.
	 * @param id The name of the sort.
	 * @param args The sort arguments.
	 * @return the sort object.
	 */
	public Sort getSort(String id, BigInteger[] indices, Sort... args) {
		SortSymbol symbol;
		symbol = mDeclaredSorts.get(id);
		if (symbol == null)
			return null;
		return symbol.getSort(indices, args);
	}

	/**
	 * Returns the Boolean sort.  This is more efficient but has the same
	 * effect as calling getSort("Bool"). 
	 * @return the Boolean sort.
	 */
	public Sort getBooleanSort() {
		return mBooleanSort;
	}
	
	/**
	 * Get the sort used to construct integers.  Note that this returns
	 * <code>null</code> if the logic does not support integers.
	 * @return Sort used for integers.
	 */
	public Sort getNumericSort() {
		return mNumericSort;
	}
	
	/**
	 * Get the sort used to construct reals.  Note that this returns
	 * <code>null</code> if the logic does not support reals.
	 * @return Sort used for reals.
	 */
	public Sort getRealSort() {
		return mRealSort;
	}
	
	/**
	 * Get the sort used to construct strings.  Note that this returns
	 * <code>null</code> if the logic does not support strings.
	 * @return Sort used for strings.
	 */
	public Sort getStringSort() {
		return mStringSort;
	}

	/******************** FUNCTIONS SYMBOLS AND FUNCTION TERMS ************/
	
	private void defineFunction(FunctionSymbolFactory factory) {
		if (mFunFactory.put(factory.mFuncName, factory) != null)
			throw new AssertionError();
	}
	
	private FunctionSymbol defineFunction(String name, Sort[] paramTypes,
			Sort resultType, TermVariable[] definitionVars, Term definition,
			int flags) {
		if ((flags & FunctionSymbol.INTERNAL) == 0) {
			if (mLogic == null)
				throw new IllegalArgumentException("Call set-logic first!");
			if (!mIsUFLogic && paramTypes.length > 0 && definition == null)
				throw new IllegalArgumentException(
						"Not allowed in this logic!");
		}
		if (mFunFactory.get(name) != null || mDeclaredFuns.get(name) != null)
			throw new IllegalArgumentException(
					"Function " + name + " is already defined.");
		FunctionSymbol f = new FunctionSymbol(name, null, paramTypes,
				resultType, definitionVars, definition, flags);	
		mDeclaredFuns.put(name, f);
		return f;
	}
	
	/**
	 * Declare a new function symbol. This corresponds to declare-fun in SMTLIB.
	 * @param name name of the function.
	 * @param paramTypes the sorts of the parameters of the function.
	 * @param resultType the sort of the result type of the function.
	 * @throws IllegalArgumentException 
	 *    if a function with that name is already defined or
	 *    if the sorts are not visible in this scope.
	 * @return the created function symbol.
	 */
	public FunctionSymbol declareFunction(
			String name, Sort[] paramTypes, Sort resultType) {
		return defineFunction(name, paramTypes, resultType, null, null, 0);
	}
	/**
	 * Defines a new function symbol.  This corresponds to define-fun in SMTLIB.
	 * @param name name of the function.
	 * @param definitionVars the variables of the function.
	 * @param definition the definition of the function.
	 * @throws IllegalArgumentException 
	 *    if a function with that name is already defined or
	 *    if the sorts are not visible in this scope.
	 * @return the created function symbol.
	 */
	public FunctionSymbol defineFunction(String name, 
			TermVariable[] definitionVars, Term definition) {
		Sort[] paramTypes = new Sort[definitionVars.length];
		for (int i = 0; i < paramTypes.length; i++)
			paramTypes[i] = definitionVars[i].getSort();
		Sort resultType = definition.getSort();
		return defineFunction(name, paramTypes, resultType, 
				definitionVars, definition, 0);
	}

	public FunctionSymbol getFunction(String name, Sort... paramTypes) {
		return getFunctionWithResult(name, null, null, paramTypes);
	}

	public FunctionSymbol getFunctionWithResult(
			String name, BigInteger[] indices, Sort resultType,
			Sort... paramTypes) {
		FunctionSymbolFactory factory = mFunFactory.get(name);
		if (factory != null) {
			FunctionSymbol fsym = factory.getFunctionWithResult(
					this, indices, paramTypes, resultType);
			if (fsym != null)
				return fsym;
			if (mLogic.isIRA()) {
				fsym = factory.getFunctionWithResult(this, indices, 
						new Sort[] {mRealSort, mRealSort}, resultType);
				if (fsym != null && fsym.typecheck(paramTypes))
					return fsym;
			}
			return null;
		}
		FunctionSymbol fsym = mDeclaredFuns.get(name);
		if (fsym != null && indices == null && resultType == null
				&& fsym.typecheck(paramTypes))
			return fsym;
		return null;
	}
	
	public ApplicationTerm term(
			FunctionSymbolFactory factory, Term... parameters) {
		Sort[] sorts = new Sort[parameters.length];
		for (int i = 0; i < parameters.length; i++)
			sorts[i] = parameters[i].getSort();
		FunctionSymbol fsym = 
			factory.getFunctionWithResult(this, null, sorts, null);
		if (fsym == null)
			throw new IllegalArgumentException(
					"Did not find overload for function " + factory);
		return term(fsym, parameters);
	}

	public ApplicationTerm term(String func, Term... parameters) {
		Sort[] paramSorts = new Sort[parameters.length];
		for (int i = 0; i < parameters.length; i++)
			paramSorts[i] = parameters[i].getSort();
		FunctionSymbol fsym =
				getFunctionWithResult(func, null, null, paramSorts);
		if (fsym == null)
			return null;
		return term(fsym, parameters);
	}

	public ApplicationTerm term(FunctionSymbol func, Term... parameters) {
		int hash = ApplicationTerm.hashApplication(func, parameters);
		for (Term t : mTermCache.iterateHashCode(hash)) {
			if (t instanceof ApplicationTerm) {
				ApplicationTerm app = (ApplicationTerm) t;
				if (func == app.getFunction()
						&& Arrays.equals(app.getParameters(),parameters))
					return app;
			}
		}
		ApplicationTerm app = new ApplicationTerm(func, parameters, hash);
		mTermCache.put(hash,app);
		return app;
	}
	
	/******************** TERM VARIABLES AND VARIABLE TERMS *****************/
	
	/**
	 * Create a fresh term variable that does not clash with any
	 * existing one.  
	 * @param prefix the prefix of the variable name (without the leading ?).
	 * @param sort   the sort of the variable.
	 * @return a fresh term variable.
	 */
	public TermVariable createFreshTermVariable(String prefix, Sort sort) {
		String name = "." + prefix + "." + mTvarCtr++;
		return new TermVariable(name, sort,
				TermVariable.hashVariable(name, sort));
	}
	
	/**
	 * Create a term variable with the given name and sort.
	 * @param name   the variable name.
	 * @param sort   the sort of the variable.
	 * @return a term variable.
	 */
	public TermVariable createTermVariable(String name,Sort sort) {
		int hash = TermVariable.hashVariable(name, sort);
		for (TermVariable tv : mTvUnify.iterateHashCode(hash)) {
			if (tv.getSort().equals(sort) && tv.getName().equals(name))
				return tv;
		}
		TermVariable tv = new TermVariable(name,sort, hash);
		mTvUnify.put(hash,tv);
		return tv;
	}
	
	public Term term(TermVariable var) {
		return var;
	}

	/******************** ANNOTATED TERMS *********************************/
	
	public Term annotatedTerm(Annotation[] annots, Term sub) {
		int hash = AnnotatedTerm.hashAnnotations(annots, sub);
		for (Term t : mTermCache.iterateHashCode(hash)) {
			if (t instanceof AnnotatedTerm) {
				AnnotatedTerm annot = (AnnotatedTerm) t;
				if (sub == annot.getSubterm()
						&& Arrays.equals(annot.getAnnotations(), annots))
					return annot;
			}
		}
		AnnotatedTerm annot = new AnnotatedTerm(annots, sub, hash);
		mTermCache.put(hash, annot);
		return annot;
	}

	/******************** ASSERTION STACK *********************************/

	public void push() {
		mDeclaredFuns.beginScope();
		mDeclaredSorts.beginScope();
	}

	public void pop() {
		mDeclaredFuns.endScope();
		mDeclaredSorts.endScope();
	}
	
	/******************** SKOLEMIZATION SUPPORT ***************************/
	public FunctionSymbol skolemize(TermVariable tv) {
		return new FunctionSymbol(
				"@" + tv.getName() + "_skolem_" + mSkolemCounter++,null,
				EMPTY_SORT_ARRAY,tv.getSort(),null,null,0);
	}
}
