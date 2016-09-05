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
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Theory.SolverSetup;

/**
 * Simple implementation of a script, that supports building terms and sorts,
 * but does not support setting and getting options, checking for satisfiabilty,
 * or getting any other results.
 *
 * This can be used as base class for implementing the script interface.
 *
 * @author Jürgen Christ, Jochen Hoenicke
 */
public class NoopScript implements Script {
	
	private Theory mTheory;
	protected int mStackLevel = 0;
	
	protected SolverSetup mSolverSetup;
	
	public NoopScript() {
		this(null, null);
	}
	
	protected NoopScript(Theory theory) {
		this(theory, null);
	}
	
	protected NoopScript(Theory theory, SolverSetup setup) {
		mTheory = theory;
		mSolverSetup = setup;
	}
	
	public Theory getTheory() {
		return mTheory;
	}

	/**
	 * Check that the symbol does not contain characters that would make
	 * it impossible to use it in a LoggingScript.  These are | and \.
	 * @param symbol the symbol to check
	 * @throws SMTLibException if symbol contains | or \.
	 */
	private void checkSymbol(String symbol) throws SMTLIBException {
		if (symbol.indexOf('|') >= 0 || symbol.indexOf('\\') >= 0) {
			throw new SMTLIBException("Symbol must not contain | or \\");
		}
	}

	@Override
	public void setLogic(String logic) throws UnsupportedOperationException {
		try {
			setLogic(Logics.valueOf(logic));
		} catch (final IllegalArgumentException eLogicUnsupported) {
			/* Logic is not in enumeration */
			throw new UnsupportedOperationException("Logic " + logic 
					+ " not supported");
		}
	}
	
	@Override
	public void setLogic(Logics logic) throws UnsupportedOperationException {
		if (mTheory != null) {
			throw new SMTLIBException("Logic already set!");
		}
		mTheory = new Theory(logic, mSolverSetup);
	}

	@Override
	public void setOption(String opt, Object value)
		throws UnsupportedOperationException, SMTLIBException {
		// Nothing to do
	}

	@Override
	public void setInfo(String info, Object value) {
		// Nothing to do
	}

	@Override
	public void declareSort(String sort, int arity) throws SMTLIBException {
		if (mTheory == null) {
			throw new SMTLIBException("No logic set!");
		}
		checkSymbol(sort);
		try {
			mTheory.declareSort(sort, arity);
		} catch (final IllegalArgumentException eiae) {
			throw new SMTLIBException(eiae.getMessage());
		}
	}

	@Override
	public void defineSort(String sort, Sort[] sortParams, Sort definition)
		throws SMTLIBException {
		if (mTheory == null) {
			throw new SMTLIBException("No logic set!");
		}
		checkSymbol(sort);
		try {
			mTheory.defineSort(sort, sortParams.length, definition);
		} catch (final IllegalArgumentException eiae) {
			throw new SMTLIBException(eiae.getMessage());
		}
	}

	@Override
	public void declareFun(String fun, Sort[] paramSorts, Sort resultSort)
		throws SMTLIBException {
		if (mTheory == null) {
			throw new SMTLIBException("No logic set!");
		}
		checkSymbol(fun);
		try {
			mTheory.declareFunction(fun, paramSorts, resultSort);
		} catch (final IllegalArgumentException eiae) {
			throw new SMTLIBException(eiae.getMessage());
		}
	}

	@Override
	public void defineFun(String fun, TermVariable[] params,
			Sort resultSort, Term definition) throws SMTLIBException {
		checkSymbol(fun);
		defineFunInternal(fun, params, resultSort, definition);
	}
	
	private void defineFunInternal(String fun, TermVariable[] params,
			Sort resultSort, Term definition) throws SMTLIBException {
		if (mTheory == null) {
			throw new SMTLIBException("No logic set!");
		}
		if (!resultSort.equalsSort(definition.getSort())) {
			throw new SMTLIBException("Sort mismatch");
		}
		try {
			mTheory.defineFunction(fun, params, definition);
		} catch (final IllegalArgumentException eiae) {
			throw new SMTLIBException(eiae.getMessage());
		}
	}

	@Override
	public void push(int levels) {
		if (mTheory == null) {
			throw new SMTLIBException("No logic set!");
		}
		mStackLevel += levels;
		for (int i = 0; i < levels; i++) {
			mTheory.push();
		}
	}

	@Override
	public void pop(int levels) throws SMTLIBException {
		if (mTheory == null) {
			throw new SMTLIBException("No logic set!");
		}
		if (levels > mStackLevel) {
			throw new SMTLIBException("Not enough levels on assertion stack");
		}
		mStackLevel -= levels;
		for (int i = 0; i < levels; i++) {
			mTheory.pop();
		}
	}

	@Override
	public LBool assertTerm(Term term) throws SMTLIBException {
		return LBool.UNKNOWN;
	}

	@Override
	public LBool checkSat() {
		return LBool.UNKNOWN;
	}
	
	@Override
	public LBool checkSatAssuming(Term... assumptions) {
		return LBool.UNKNOWN;
	}

	@Override
	public Term[] getAssertions() throws SMTLIBException {
		throw new UnsupportedOperationException();
	}

	@Override
	public Term getProof() throws SMTLIBException,
			UnsupportedOperationException {
		throw new UnsupportedOperationException();			
	}

	@Override
	public Term[] getUnsatCore() throws SMTLIBException,
			UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public Map<Term, Term> getValue(Term[] terms) throws SMTLIBException,
			UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public Assignments getAssignment() throws SMTLIBException,
			UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public Object getOption(String opt)
		throws UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public Object getInfo(String info)
		throws UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public Term simplify(Term term) throws SMTLIBException {
		throw new UnsupportedOperationException();
	}

	@Override
	public void reset() {
		mTheory = null;
		mStackLevel = 0;
	}

	@Override
	public Term[] getInterpolants(Term[] partition) throws SMTLIBException,
			UnsupportedOperationException {
		// The default startOfSubtrees is an array with 0's.
		final int[] startOfSubtrees = new int[partition.length];
		return getInterpolants(partition, startOfSubtrees);
	}

	@Override
	public Term[] getInterpolants(Term[] partition, int[] startOfSubtree)
		throws SMTLIBException, UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public void exit() {
		// Nothing to do
	}

	@Override
	public Sort sort(String sortname, Sort... params) throws SMTLIBException {
		return sort(sortname, null, params);
	}

	@Override
	public Sort sort(String sortname, BigInteger[] indices, Sort... params)
		throws SMTLIBException {
		if (mTheory == null) {
			throw new SMTLIBException("No logic set!");
		}
		final Sort res = mTheory.getSort(sortname, indices, params);
		if (res == null) {
			throw new SMTLIBException("Sort " + sortname + " not declared");
		}
		return res;
	}

	@Override
	public Term term(String funcname, Term... params) throws SMTLIBException {
		return term(funcname, null, null, params);
	}

	@Override
	public Term term(String funcname, BigInteger[] indices,
			Sort returnSort, Term... params) throws SMTLIBException {
		if (mTheory == null) {
			throw new SMTLIBException("No logic set!");
		}
		final Sort[] sorts =
				params.length == 0 ? Script.EMPTY_SORT_ARRAY : new Sort[params.length];
		for (int i = 0; i < sorts.length; i++) {
			sorts[i] = params[i].getSort();
		}
		final FunctionSymbol fsym = mTheory
				.getFunctionWithResult(funcname, indices, returnSort, sorts);
		if (fsym == null) {
			final StringBuilder sb = new StringBuilder();
			final PrintTerm pt = new PrintTerm();
			sb.append("Undeclared function symbol (").append(funcname);
			for (final Sort s: sorts) {
				sb.append(' ');
				pt.append(sb, s);
			}
			sb.append(')');
			throw new SMTLIBException(sb.toString());
		}
		return mTheory.term(fsym, params);
	}
	
	@Override
	public TermVariable variable(String varname, Sort sort)
		throws SMTLIBException {
		if (sort == null || varname == null) {
			throw new SMTLIBException(
					"Invalid input to create a term variable");
		}
		checkSymbol(varname);
		return mTheory.createTermVariable(varname, sort);
	}

	@Override
	public Term quantifier(int quantor, TermVariable[] vars, Term body,
			Term[]... patterns) throws SMTLIBException {
		if (vars.length == 0) {
			throw new SMTLIBException("No quantified variables given");
		}
		if (body == null) {
			throw new SMTLIBException("Empty quantifier body");
		}
		if (patterns != null && patterns.length > 0) {
			final Annotation[] annots = new Annotation[patterns.length];
			int i = 0;
			for (final Term[] p : patterns) {
				annots[i++] = new Annotation(":pattern", p);
			}
			body = mTheory.annotatedTerm(annots, body);
		}
		if (quantor == Script.EXISTS) {
			return mTheory.exists(vars, body);
		}
		if (quantor == Script.FORALL) {
			return mTheory.forall(vars, body);
		}
		throw new SMTLIBException("Unknown Quantifier");
	}

	@Override
	public Term let(TermVariable[] vars, Term[] values, Term body)
		throws SMTLIBException {
		if (vars.length != values.length) {
			throw new SMTLIBException(
					"Need exactly one value for every variable");
		}
		return mTheory.let(vars, values, body);
	}

	@Override
	public Term annotate(Term t, Annotation... annotations)
		throws SMTLIBException {
		if (annotations.length > 0) {
			for (final Annotation a : annotations) {
				if (a.getKey().equals(":named")) {
					if (!(a.getValue() instanceof String)) {
						throw new SMTLIBException(
								"Need a string value for :named");
					}
					checkSymbol((String) a.getValue());
					if (t.getFreeVars().length != 0) {
						throw new SMTLIBException("Cannot name open terms");
					} else {
						defineFunInternal((String) a.getValue(), 
								Theory.EMPTY_TERM_VARIABLE_ARRAY, t.getSort(), t);
					}
				}
			}
			return mTheory.annotatedTerm(annotations, t);
		} else {
			return t;
		}
	}

	@Override
	public Term numeral(String num) throws SMTLIBException {
		if (mTheory == null) {
			throw new SMTLIBException("No logic set!");
		}
		if (mTheory.getNumericSort() == null) {
			throw new SMTLIBException("Logic does not allow numerals");
		}
		try {
			return mTheory.numeral(num);
		} catch (final NumberFormatException enfe) {
			throw new SMTLIBException("Not a numeral: " + num);
		}
	}
	
	@Override
	public Term numeral(BigInteger num) throws SMTLIBException {
		if (mTheory == null) {
			throw new SMTLIBException("No logic set!");
		}
		if (mTheory.getNumericSort() == null) {
			throw new SMTLIBException("Logic does not allow numerals");
		}
		return mTheory.numeral(num);
	}

	@Override
	public Term decimal(String decimal) throws SMTLIBException {
		if (mTheory == null) {
			throw new SMTLIBException("No logic set!");
		}
		if (mTheory.getRealSort() == null) {
			throw new SMTLIBException("Logic does not allow reals");
		}
		try {
			return mTheory.decimal(decimal);
		} catch (final NumberFormatException enfe) {
			throw new SMTLIBException("Not a decimal: " + decimal);
		}
	}

	@Override
	public Term decimal(BigDecimal decimal) throws SMTLIBException {
		if (mTheory == null) {
			throw new SMTLIBException("No logic set!");
		}
		if (mTheory.getRealSort() == null) {
			throw new SMTLIBException("Logic does not allow reals");
		}
		return mTheory.decimal(decimal);
	}

	@Override
	public Term string(String str) throws SMTLIBException {
		if (mTheory == null) {
			throw new SMTLIBException("No logic set!");
		}
		if (mTheory.getStringSort() == null) {
			throw new SMTLIBException("Logic does not allow strings");
		}
		return mTheory.string(str);
	}

	@Override
	public Term hexadecimal(String hex) throws SMTLIBException {
		if (mTheory == null) {
			throw new SMTLIBException("No logic set!");
		}
		final Term res = mTheory.hexadecimal(hex);
		if (res == null) {
			throw new SMTLIBException("No bitvector logic");
		}
		return res;
	}

	@Override
	public Term binary(String bin) throws SMTLIBException {
		if (mTheory == null) {
			throw new SMTLIBException("No logic set!");
		}
		final Term res = mTheory.binary(bin);
		if (res == null) {
			throw new SMTLIBException("No bitvector logic");
		}
		return res;
	}
		
	@Override
	public Sort[] sortVariables(String... names) throws SMTLIBException {
		if (mTheory == null) {
			throw new SMTLIBException("No logic set!");
		}
		return mTheory.createSortVariables(names);
	}
	
	@Override
	public Model getModel() throws SMTLIBException,
			UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterable<Term[]> checkAllsat(Term[] predicates)
		throws SMTLIBException,	UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public Term[] findImpliedEquality(Term[] x, Term[] y)
		throws SMTLIBException,	UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public QuotedObject echo(QuotedObject msg) {
		return msg;
	}

	@Override
	public void resetAssertions() {
		if (mTheory == null) {
			throw new SMTLIBException("No logic set!");
		}
		mTheory.resetAssertions();
		mStackLevel = 0;
	}

	@Override
	public Term[] getUnsatAssumptions() throws SMTLIBException,
			UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

}
