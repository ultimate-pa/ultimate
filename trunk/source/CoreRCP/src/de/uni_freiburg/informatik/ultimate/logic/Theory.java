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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;
import de.uni_freiburg.informatik.ultimate.util.UnifyHash;


/**
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
	
	private SolverSetup m_SolverSetup;
	private Logics m_Logic;
	private boolean m_IsUFLogic;
	private Sort m_NumericSort, m_RealSort, m_StringSort, m_BooleanSort;
	private SortSymbol m_BitVecSort;
	private HashMap<String, FunctionSymbolFactory> m_FunFactory = 
		new HashMap<String, FunctionSymbolFactory>();

	ScopedHashMap<String, SortSymbol> m_DeclaredSorts = 
		new ScopedHashMap<String, SortSymbol>();
	ScopedHashMap<String, FunctionSymbol> m_DeclaredFuns = 
		new ScopedHashMap<String, FunctionSymbol>();
	
	private UnifyHash<QuantifiedFormula> m_QfCache = new UnifyHash<QuantifiedFormula>();
	private UnifyHash<LetTerm> m_LetCache = new UnifyHash<LetTerm>();
	private UnifyHash<Term> m_TermCache = new UnifyHash<Term>();
	private UnifyHash<TermVariable> m_TvUnify = new UnifyHash<TermVariable>();
	
	public final ApplicationTerm TRUE, FALSE;
	public final FunctionSymbol m_And, m_Or, m_Not, m_Implies, m_Xor;
	public final PolymorphicFunctionSymbol m_Equals, m_Distinct, m_Ite;
	
	private final static Sort[] EMPTY_SORT_ARRAY = {};
	
	private int m_TvarCtr = 0;
	
	private int m_SkolemCounter = 0;
	
	public Theory() {
		m_IsUFLogic = false;
		TRUE = FALSE = null;
		m_And = m_Or = m_Not = m_Implies = m_Xor = null;
		m_Equals = m_Distinct = m_Ite = null;
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
		m_SolverSetup = solverSetup;
		Sort[] noarg = new Sort[0];
		m_BooleanSort = declareInternalSort("Bool", 0, 0).getSort(
				null, noarg);
		Sort[] generic1 = createSortVariables("A");
		Sort[] bool1 = new Sort[] { m_BooleanSort};
		Sort[] bool2 = new Sort[] { m_BooleanSort, m_BooleanSort};
		Sort[] generic2 = new Sort[] { generic1[0], generic1[0] };
		int leftassoc = FunctionSymbol.LEFTASSOC;
		m_Not = declareInternalFunction("not", bool1, m_BooleanSort, 0);
		m_And = declareInternalFunction("and", bool2, m_BooleanSort, leftassoc);
		m_Or  = declareInternalFunction("or",  bool2, m_BooleanSort, leftassoc); 
		m_Implies = declareInternalFunction("=>",  bool2, m_BooleanSort, FunctionSymbol.RIGHTASSOC);
		m_Equals = declareInternalPolymorphicFunction("=", generic1, generic2,
				m_BooleanSort, FunctionSymbol.CHAINABLE);
		m_Distinct = declareInternalPolymorphicFunction("distinct", generic1, generic2,
				m_BooleanSort, FunctionSymbol.PAIRWISE);
		m_Xor = declareInternalFunction("xor", bool2, m_BooleanSort, leftassoc);
		m_Ite = declareInternalPolymorphicFunction("ite", generic1, new Sort[] { m_BooleanSort, generic1[0], generic1[0] },
				generic1[0], 
				0);
		TRUE  = term(declareInternalFunction("true", noarg, m_BooleanSort, 0)); 
		FALSE = term(declareInternalFunction("false", noarg, m_BooleanSort, 0));
		// Finally, declare logic specific functions
		setLogic(logic);
	}

	/******************** LOGICAL OPERATORS *******************************/
	
	private Term simplifyAndOr(FunctionSymbol connector, Term... subforms)
	{
		Term neutral = (connector == m_And ? TRUE : FALSE);
		List<Term> formulas = new ArrayList<Term>();
		
		for (Term f : subforms) {
			if (f == TRUE || f == FALSE) {
				if (f == neutral)
					continue;
				else
					return f;
			}

			/* Normalize nested and/ors */
			if (f instanceof ApplicationTerm
				&& ((ApplicationTerm) f).getFunction() == connector) {
				for (Term subf : ((ApplicationTerm) f).getParameters())
					if (!formulas.contains(subf))
						formulas.add(subf);
			} else if (!formulas.contains(f)) {
				formulas.add(f);
			}
		}
		if (formulas.size() <= 1) {
			if (formulas.isEmpty())
				return neutral;
			else
				return formulas.get(0);
		}
		Term[] arrforms = formulas.toArray(new Term[formulas.size()]);
		return term(connector, arrforms);
	}

	public Term not(Term f)
	{
		if (f == TRUE) return FALSE;
		if (f == FALSE) return TRUE;
		if (f instanceof ApplicationTerm
			&& ((ApplicationTerm)f).getFunction() == m_Not)
			return ((ApplicationTerm) f).getParameters()[0];
		return term(m_Not, f);
	}

	public Term and(Term... subforms) {
		return simplifyAndOr(m_And, subforms);
	}
	public Term or(Term... subforms) {
		return simplifyAndOr(m_Or, subforms);
	}

	public Term implies(Term f, Term g)
	{ 
		if (g == TRUE || f == TRUE) return g;
		if (f == FALSE) return TRUE;
		if (g == FALSE) return not(f);
		if( f == g ) return TRUE;
		return term(m_Implies, f, g);
	}

	public Term xor(Term f, Term g)
	{ 
		if (f == TRUE) return not(g);
		if (g == TRUE) return not(f);
		if (f == FALSE) return g;
		if (g == FALSE) return f;
		if( f == g ) return FALSE;
		return term(m_Xor, f, g);
	}

	public Term ifthenelse(Term c, Term t, Term e)
	{
		if (c == TRUE)  return t;
		if (c == FALSE) return e;
		if (t == e) return t;
		if (t == TRUE && e == FALSE)
			return c;
		if (t == FALSE && e == TRUE)
			return not(c);
		if (t == TRUE)
			return term(m_Or, c, e);
		if (t == FALSE)
			return term(m_And, term(m_Not, c), e);
		if (e == TRUE)
			return term(m_Implies, c, t);
		if (e == FALSE)
			return term(m_And, c, t);
		return term(m_Ite, c, t, e);
	}

	private Term quantify(int quant, TermVariable[] vars, Term f) {
		if (f == TRUE || f == FALSE)
			return f;
		int hash = QuantifiedFormula.hashQuantifier(quant, vars, f);
		for (QuantifiedFormula qf : m_QfCache.iterateHashCode(hash)) {
			if (qf.getQuantifier() == quant && qf.getSubformula() == f 
				&& Arrays.equals(vars,qf.getVariables()))
				return qf;
		}
		QuantifiedFormula qf = 
			new QuantifiedFormula(quant, vars, f, hash);
		m_QfCache.put(hash,qf);
		return qf;
	}
	public Term exists(TermVariable[] vars, Term f)
	{
		return quantify(QuantifiedFormula.EXISTS, vars, f);
	}
	public Term forall(TermVariable[] vars, Term f)
	{
		return quantify(QuantifiedFormula.FORALL, vars, f);
	}
	
	public Term let(TermVariable[] vars, Term[] values, Term subform) {
		assert (vars.length == values.length);
		if (vars.length == 0)
			return subform;
		int hash = LetTerm.hashLet(vars, values, subform);
		for (LetTerm lt : m_LetCache.iterateHashCode(hash)) {
			if (lt.getSubTerm() == subform
				&& Arrays.equals(lt.getVariables(), vars)
				&& Arrays.equals(lt.getValues(), values))
				return lt;
		}
		LetTerm lf = new LetTerm(vars, values, subform, hash);
		m_LetCache.put(hash,lf);
		return lf;
	}

	public Term let(TermVariable var, Term value, Term subform) {
		return let(new TermVariable[] {var}, new Term[]{value}, subform);
	}

	public Term distinct(Term... terms)
	{
		if (terms.length < 2)
			return null;
		if (terms.length == 2) {
			if (terms[0] == terms[1])
				return FALSE;
			if (terms[0].getSort() == m_BooleanSort) {
				if (terms[0] == FALSE) return terms[1];
				if (terms[1] == FALSE) return terms[0];
				if (terms[0] == TRUE) return not(terms[1]);
				if (terms[1] == TRUE) return not(terms[0]);
			}
			return term(m_Distinct, terms);
		}
		HashSet<Term> params = new HashSet<Term>(Arrays.asList(terms));
		if (params.size() != terms.length)
			// We had something like (distinct ... a ... a ...)
			return FALSE;
		return term(m_Distinct, terms);
	}
	public Term equals(Term... terms)
	{
		if (terms.length < 2)
			return null;
		if (terms.length == 2) {
			if (terms[0] == terms[1])
				return TRUE;
			if (terms[0].getSort() == m_BooleanSort) {
				if (terms[0] == TRUE) return terms[1];
				if (terms[1] == TRUE) return terms[0];
				if (terms[0] == FALSE) return not(terms[1]);
				if (terms[1] == FALSE) return not(terms[0]);
			}
			return term(m_Equals, terms);
		}
		HashSet<Term> params = new HashSet<Term>(Arrays.asList(terms));
		if (params.size() == 1)
			// We had (= a a ... a)
			return TRUE;
		return term(m_Equals, terms);
	}

	/******************** CONSTANTS *************************************/

	public Term constant(Object value, Sort sort) {
		int hash = ConstantTerm.hashConstant(value, sort);
		for (Term t : m_TermCache.iterateHashCode(hash) ) {
			if( t instanceof ConstantTerm ) {
				ConstantTerm nt = (ConstantTerm)t;
				if( nt.getSort() == sort && value.equals(nt.getValue()) )
					return  nt;
			}
		}
		ConstantTerm nt = new ConstantTerm(value, sort, hash);
		m_TermCache.put(hash,nt);
		return nt;
	}
	
	public Term numeral(BigInteger num) {
		Term result = constant(num.abs(), m_NumericSort);
		if (num.signum() < 0) {
			FunctionSymbol neg = getFunction("-", m_NumericSort);
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
		Term result = constant(value.abs(), m_RealSort);
		if (value.signum() < 0) {
			FunctionSymbol neg = getFunction("-", m_RealSort);
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
		if (sort == m_RealSort) {
			return rational(c.numerator(), c.denominator());
		} else {
			assert c.isIntegral();
			return numeral(c.numerator());
		}
	}

	public Term binary(String value) {
		assert value.startsWith("#b");
		if (m_BitVecSort == null)
			return null;
		BigInteger bsize = BigInteger.valueOf(value.length()-2);
		Sort sort = m_BitVecSort.getSort(new BigInteger[] { bsize }, new Sort[0]);
		return new ConstantTerm(value, sort,
				ConstantTerm.hashConstant(value, sort));
	}
	
	public Term hexadecimal(String value) {
		assert value.startsWith("#x");
		if (m_BitVecSort == null)
			return null;
		BigInteger bsize = BigInteger.valueOf(4*(value.length()-2));
		Sort sort = m_BitVecSort.getSort(new BigInteger[] { bsize }, new Sort[0]);
		return new ConstantTerm(value, sort,
				ConstantTerm.hashConstant(value, sort));
	}
	
	public Term rational(BigInteger num,BigInteger denom) {
		BigInteger gcd = num.gcd(denom);
		if (denom.signum() * gcd.signum() < 0)
			gcd = gcd.negate();
		num = num.divide(gcd);
		denom = denom.divide(gcd);
		
		if (denom.equals(BigInteger.ONE)) {
			return decimal(new BigDecimal(num));
		} else {
			FunctionSymbol div = getFunction("/", m_NumericSort, m_NumericSort);
			return term(div, numeral(num), numeral(denom));
		}
	}
	
	public Term string(String value) {
		return constant(new QuotedObject(value), m_StringSort);
	}

	/******************** LOGICS AND THEORIES ********************************/
	public Logics getLogic() {
		return m_Logic;
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
		assert !m_FunFactory.containsKey(name);
		PolymorphicFunctionSymbol f = new PolymorphicFunctionSymbol
				(name, sortParams, paramTypes, resultType, flags | FunctionSymbol.INTERNAL);
		defineFunction(f);
		return f;
	}
	
	class MinusFunctionFactory extends FunctionSymbolFactory {
		Sort m_Sort1, m_Sort2;
		public MinusFunctionFactory(Sort sort1, Sort sort2) {
			super("-");
			m_Sort1 = sort1;
			m_Sort2 = sort2;
		}

		public int getFlags(BigInteger[] indices, Sort[] paramSorts, Sort resultSort) {
			return paramSorts.length == 1 ?  FunctionSymbol.INTERNAL
					: FunctionSymbol.LEFTASSOC | FunctionSymbol.INTERNAL;
		}

		@Override
		public Sort getResultSort(BigInteger[] indices, Sort[] paramSorts,
				Sort resultSort) {
			if (indices != null 
				|| paramSorts.length == 0 || paramSorts.length > 2	
				|| resultSort != null
				|| (paramSorts[0] != m_Sort1 && paramSorts[0] != m_Sort2))
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

		public Sort getResultSort(BigInteger[] indices, Sort[] paramSorts, Sort resultSort) {
			return indices != null && indices.length == 1 && indices[0].signum() > 0
					&& paramSorts.length == 1 && paramSorts[0] == m_NumericSort
					&& resultSort == null ? m_BooleanSort : null;
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
			declareInternalFunction("div", sort2, sort, FunctionSymbol.LEFTASSOC);
			declareInternalFunction("mod", sort2, sort, 0);
			defineFunction(new DivisibleFunctionFactory());
		}
		Sort sBool = m_BooleanSort;
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
			Sort m_ReturnSort;
			int m_Flags;
			BinArithFactory(String name, Sort returnSort, int flags) {
				super(name);
				m_ReturnSort = returnSort;
				m_Flags = flags | FunctionSymbol.INTERNAL;
			}

			public int getFlags(BigInteger[] indices, Sort[] paramSorts, Sort resultSort) {
				return m_Flags;
			}

			public Sort getResultSort(BigInteger[] indices, Sort[] paramSorts, Sort resultSort) {
				if (indices == null
					&& paramSorts.length == 2
					&& paramSorts[0] == paramSorts[1]
					&& (paramSorts[0] == m_NumericSort || paramSorts[0] == m_RealSort)
					&& resultSort == null) {
					return m_ReturnSort != null ? m_ReturnSort : paramSorts[0];
				} else {
					return null;
				}
			}
		}
		
		defineFunction(new BinArithFactory("+", null, FunctionSymbol.LEFTASSOC));
		defineFunction(new MinusFunctionFactory(m_NumericSort, m_RealSort));
		defineFunction(new BinArithFactory("*", null, FunctionSymbol.LEFTASSOC));
		defineFunction(new BinArithFactory(">", m_BooleanSort, FunctionSymbol.CHAINABLE));
		defineFunction(new BinArithFactory(">=", m_BooleanSort, FunctionSymbol.CHAINABLE));
		defineFunction(new BinArithFactory("<", m_BooleanSort, FunctionSymbol.CHAINABLE));
		defineFunction(new BinArithFactory("<=", m_BooleanSort, FunctionSymbol.CHAINABLE));

		Sort[] int1  = new Sort[] { m_NumericSort };
		Sort[] int2  = new Sort[] { m_NumericSort, m_NumericSort };
		Sort[] real1 = new Sort[] { m_RealSort };
		Sort[] real2 = new Sort[] { m_RealSort, m_RealSort };
		declareInternalFunction("/", real2, m_RealSort, FunctionSymbol.LEFTASSOC);
		declareInternalFunction("div", int2, m_NumericSort, FunctionSymbol.LEFTASSOC);
		defineFunction(new DivisibleFunctionFactory());
		declareInternalFunction("to_real", int1, m_RealSort, 0);
		declareInternalFunction("to_int", real1, m_NumericSort, 0);

		declareInternalFunction("mod", int2, m_NumericSort, 0);
		TermVariable xr = createTermVariable("x1", m_RealSort);
		// isint x: (= x (to_real (to_int x)))
		Term isintx = term("=", xr, term("to_real", term("to_int", xr)));
		declareInternalFunction("is_int", real1, 
				new TermVariable[]{ xr }, isintx, 0);

		defineFunction(new FunctionSymbolFactory("abs") {
			public Term getDefinition(TermVariable[] tvs, Sort resultSort) {
				Term zero = (resultSort == m_NumericSort) ? numeral("0")
							: decimal("0.0");
				// abs x: (ite (>= x 0) x (- x))
				return term("ite", term(">=", tvs[0], zero), 
							tvs[0], term("-", tvs[0]));
			}

			public Sort getResultSort(BigInteger[] indices, Sort[] paramSorts, Sort resultSort) {
				if (indices == null
					&& paramSorts.length == 1
					&& (paramSorts[0] == m_NumericSort || paramSorts[0] == m_RealSort)
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
		SortSymbol arraySort = declareInternalSort("Array", 2, SortSymbol.ARRAY);
		Sort array = arraySort.getSort(null, generic2);
		declareInternalPolymorphicFunction("select", generic2, new Sort[] { array, generic2[0] }, 
				generic2[1], 0);
		declareInternalPolymorphicFunction("store", generic2, new Sort[] { array, generic2[0], generic2[1] },
				array, 0);
	}
	
	private void createBitVecOperators() {
		m_BitVecSort = new SortSymbol(this, "BitVec", 0, null, SortSymbol.INTERNAL | SortSymbol.INDEXED) {
			public void checkArity(BigInteger[] indices, int arity) {
				if (indices == null || indices.length != 1)
					throw new IllegalArgumentException("BitVec needs one index");
				if (indices[0].signum() <= 0)
					throw new IllegalArgumentException("BitVec index must be positive");
				if (arity != 0)
					throw new IllegalArgumentException("BitVec has no parameters");
			}
		};
		m_DeclaredSorts.put("BitVec", m_BitVecSort);
		class RegularBitVecFunction extends FunctionSymbolFactory {
			int m_NumArgs;
			Sort m_Result;
			public RegularBitVecFunction(String name, int numArgs, Sort result) {
				super(name);
				m_NumArgs = numArgs;
				m_Result = result;
			}
			@Override
			public Sort getResultSort(BigInteger[] indices, Sort[] paramSorts,
					Sort resultSort) {
				if (indices != null
					|| paramSorts.length != m_NumArgs || resultSort != null
					|| paramSorts[0].getName() != "BitVec")
					return null;
				for (int i = 1; i < m_NumArgs; i++)
					if (paramSorts[i] != paramSorts[0])
						return null;
				return m_Result != null ? m_Result : paramSorts[0];
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
				return m_BitVecSort.getSort(new BigInteger[] { size }, new Sort[0]);
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
				return m_BitVecSort.getSort(new BigInteger[] { size }, new Sort[0]);
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
				return m_BitVecSort.getSort(new BigInteger[] { size }, new Sort[0]);
			}
		});
		Sort bitvec1 = m_BitVecSort.
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
				BigInteger size = indices[0].multiply(paramSorts[0].getIndices()[0]);
				return m_BitVecSort.getSort(new BigInteger[] { size }, new Sort[0]);
			}
		});
		defineFunction(new ExtendBitVecFunction("zero_extend"));
		defineFunction(new ExtendBitVecFunction("sign_extend"));
		defineFunction(new RotateBitVecFunction("rotate_left"));
		defineFunction(new RotateBitVecFunction("rotate_right"));
		
		defineFunction(new RegularBitVecFunction("bvult", 2, m_BooleanSort));
		defineFunction(new RegularBitVecFunction("bvule", 2, m_BooleanSort));
		defineFunction(new RegularBitVecFunction("bvugt", 2, m_BooleanSort));
		defineFunction(new RegularBitVecFunction("bvuge", 2, m_BooleanSort));
		defineFunction(new RegularBitVecFunction("bvslt", 2, m_BooleanSort));
		defineFunction(new RegularBitVecFunction("bvsle", 2, m_BooleanSort));
		defineFunction(new RegularBitVecFunction("bvsgt", 2, m_BooleanSort));
		defineFunction(new RegularBitVecFunction("bvsge", 2, m_BooleanSort));
	}
	
	private void setLogic(Logics logic) {
		this.m_Logic = logic;
		switch (logic) {
		case CORE:
			break;
		case QF_AX:
			createArrayOperators();
			break;
		case AUFLIA:
		case QF_AUFLIA:
			createArrayOperators();
		case UFNIA:
		case QF_UFLIA:
		case QF_UFIDL:
			m_IsUFLogic = true;
		case QF_NIA:
		case QF_IDL:
		case QF_LIA:
			m_NumericSort = declareInternalSort(
					"Int", 0, SortSymbol.NUMERIC).getSort(null, new Sort[0]);
			createNumericOperators(m_NumericSort, false);
			break;
		case UFLRA:
		case QF_UFLRA:
		case QF_UFNRA:
			m_IsUFLogic = true;
		case LRA:
		case QF_NRA:
		case QF_LRA:
		case QF_RDL:
			m_RealSort = m_NumericSort = 
				declareInternalSort("Real", 0, SortSymbol.NUMERIC).getSort(
						null, new Sort[0]);
			createNumericOperators(m_RealSort, true);
			break;
		case QF_UF:
			m_IsUFLogic = true;
			break;
		case AUFLIRA:
		case AUFNIRA:
			createArrayOperators();
		case QF_UFLIRA:
			m_IsUFLogic = true;
			m_RealSort = declareInternalSort(
					"Real", 0, SortSymbol.NUMERIC).getSort(null, new Sort[0]);
			m_NumericSort = declareInternalSort(
					"Int", 0, SortSymbol.NUMERIC).getSort(null, new Sort[0]);
			createIRAOperators();
			break;
		case QF_AUFBV:
			createArrayOperators();
		case QF_UFBV:
			m_IsUFLogic = true;
		case QF_BV:
			createBitVecOperators();
			break;
		case QF_ABV:
			createArrayOperators();
			createBitVecOperators();
			break;
		}
		if (m_SolverSetup != null)
			m_SolverSetup.setLogic(this, logic);
	}
	
	/******************** SORTS ********************************************/
	
	private SortSymbol defineSort(String name, int paramCount, Sort definition, 
				  int flags) {
		if (!m_IsUFLogic && m_Logic != Logics.QF_AX 
				&& (flags & FunctionSymbol.INTERNAL) == 0)
			throw new IllegalArgumentException("Not allowed in this logic");
		SortSymbol sortsym = m_DeclaredSorts.get(name);
		if (sortsym != null)
			throw new IllegalArgumentException("Sort "+name+" already exists.");
		sortsym = new SortSymbol(this, name, paramCount, definition, flags); 
		m_DeclaredSorts.put(name, sortsym);
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
			sorts[i] = new SortSymbol(this, names[i], i, null, SortSymbol.TYPEPARAM).
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
		symbol = m_DeclaredSorts.get(id);
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
		return m_BooleanSort;
	}
	
	/**
	 * Get the sort used to construct integers.  Note that this returns
	 * <code>null</code> if the logic does not support integers.
	 * @return Sort used for integers.
	 */
	public Sort getNumericSort() {
		return m_NumericSort;
	}
	
	/**
	 * Get the sort used to construct reals.  Note that this returns
	 * <code>null</code> if the logic does not support reals.
	 * @return Sort used for reals.
	 */
	public Sort getRealSort() {
		return m_RealSort;
	}
	
	/**
	 * Get the sort used to construct strings.  Note that this returns
	 * <code>null</code> if the logic does not support strings.
	 * @return Sort used for strings.
	 */
	public Sort getStringSort() {
		return m_StringSort;
	}

	/******************** FUNCTIONS SYMBOLS AND FUNCTION TERMS ************/
	
	private void defineFunction(FunctionSymbolFactory factory)
	{
		if (m_FunFactory.put(factory.m_FuncName, factory) != null)
			throw new AssertionError();
	}
	
	private FunctionSymbol defineFunction(String name, Sort[] paramTypes, Sort resultType,
			TermVariable[] definitionVars, Term definition, int flags)
	{
		if ((flags & FunctionSymbol.INTERNAL) == 0) {
			if (m_Logic == null)
				throw new IllegalArgumentException("Call set-logic first!");
			if (!m_IsUFLogic && paramTypes.length > 0 && definition == null)
				throw new IllegalArgumentException("Not allowed in this logic!");
		}
		if (m_FunFactory.get(name) != null || m_DeclaredFuns.get(name) != null)
			throw new IllegalArgumentException("Function "+name+" is already defined.");
		FunctionSymbol f = new FunctionSymbol
				(name, null, paramTypes, resultType, definitionVars, definition, flags);	
		m_DeclaredFuns.put(name, f);
		return f;
	}
	
	/**
	 * Declare a new function symbol. This corresponds to declare-fun in SMT-lib. 
	 * @param name name of the function.
	 * @param paramTypes the sorts of the parameters of the function.
	 * @param resultType the sort of the result type of the function.
	 * @throws IllegalArgumentException 
	 *    if a function with that name is already defined or
	 *    if the sorts are not visible in this scope.
	 * @return the created function symbol.
	 */
	public FunctionSymbol declareFunction(String name, Sort[] paramTypes, Sort resultType) {
		return defineFunction(name, paramTypes, resultType, null, null, 0);
	}
	/**
	 * Defines a new function symbol.  This corresponds to define-fun in SMT-lib. 
	 * @param name name of the function.
	 * @param paramTypes the sorts of the parameters of the function.
	 * @param resultType the sort of the result type of the function.
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

	public FunctionSymbol getFunctionWithResult
		(String name, BigInteger[] indices, Sort resultType, Sort... paramTypes) {
		FunctionSymbolFactory factory = m_FunFactory.get(name);
		if (factory != null) {
			FunctionSymbol fsym = factory.getFunctionWithResult(this, indices, paramTypes, resultType);
			if (fsym != null)
				return fsym;
			if (m_Logic.isIRA()) {
				fsym = factory.getFunctionWithResult(this, indices, 
						new Sort[] {m_RealSort, m_RealSort}, resultType);
				if (fsym != null && fsym.typecheck(paramTypes))
					return fsym;
			}
			return null;
		}
		FunctionSymbol fsym = m_DeclaredFuns.get(name);
		if (fsym != null && indices == null && resultType == null
				&& fsym.typecheck(paramTypes))
			return fsym;
		return null;
	}
	
	public ApplicationTerm term(FunctionSymbolFactory factory, Term... parameters) {
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
		FunctionSymbol fsym = getFunctionWithResult(func, null, null, paramSorts);
		if (fsym == null)
			return null;
		return term(fsym, parameters);
	}

	public ApplicationTerm term(FunctionSymbol func, Term... parameters) {
		int hash = ApplicationTerm.hashApplication(func, parameters);
		for (Term t : m_TermCache.iterateHashCode(hash)) {
			if (t instanceof ApplicationTerm) {
				ApplicationTerm app = (ApplicationTerm) t;
				if (func == app.getFunction()
						&& Arrays.equals(app.getParameters(),parameters))
					return app;
			}
		}
		ApplicationTerm app = new ApplicationTerm(func, parameters, hash);
		m_TermCache.put(hash,app);
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
		String name = "."+prefix+"."+m_TvarCtr++;
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
		for (TermVariable tv : m_TvUnify.iterateHashCode(hash)) {
			if( tv.getSort().equals(sort) && tv.getName().equals(name) )
				return tv;
		}
		TermVariable tv = new TermVariable(name,sort, hash);
		m_TvUnify.put(hash,tv);
		return tv;
	}
	
	public Term term(TermVariable var) {
		return var;
	}

	/******************** ANNOTATED TERMS *********************************/
	
	public Term annotatedTerm(Annotation[] annots, Term sub) {
		int hash = AnnotatedTerm.hashAnnotations(annots, sub);
		for (Term t : m_TermCache.iterateHashCode(hash)) {
			if (t instanceof AnnotatedTerm) {
				AnnotatedTerm annot = (AnnotatedTerm) t;
				if (sub == annot.getSubterm()
						&& Arrays.equals(annot.getAnnotations(), annots))
					return annot;
			}
		}
		AnnotatedTerm annot = new AnnotatedTerm(annots, sub, hash);
		m_TermCache.put(hash, annot);
		return annot;
	}

	/******************** ASSERTION STACK *********************************/

	public void push() {
		m_DeclaredFuns.beginScope();
		m_DeclaredSorts.beginScope();
	}

	public void pop() {
		m_DeclaredFuns.endScope();
		m_DeclaredSorts.endScope();
	}

	/******************** SKOLEMIZATION SUPPORT ***************************/
	// TODO Check for overflows in the m_SkolemCounter
	public FunctionSymbol skolemize(TermVariable tv) {
		return new FunctionSymbol(
				"@" + tv.getName() + "_skolem_" + m_SkolemCounter++,null,
				EMPTY_SORT_ARRAY,tv.getSort(),null,null,0);
	}
}
