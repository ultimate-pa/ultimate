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

import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
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

	protected NoopScript(final Theory theory) {
		this(theory, null);
	}

	protected NoopScript(final Theory theory, final SolverSetup setup) {
		mTheory = theory;
		mSolverSetup = setup;
	}

	@Override
	public Theory getTheory() {
		return mTheory;
	}

	/**
	 * Check that the symbol does not contain characters that would make
	 * it impossible to use it in a LoggingScript.  These are | and \.
	 * @param symbol the symbol to check
	 * @throws SMTLibException if symbol contains | or \.
	 */
	private void checkSymbol(final String symbol) throws SMTLIBException {
		if (symbol.indexOf('|') >= 0 || symbol.indexOf('\\') >= 0) {
			throw new SMTLIBException("Symbol must not contain | or \\");
		}
	}

	@Override
	public void setLogic(final String logic) throws UnsupportedOperationException {
		try {
			setLogic(Logics.valueOf(logic));
		} catch (final IllegalArgumentException eLogicUnsupported) {
			/* Logic is not in enumeration */
			throw new UnsupportedOperationException("Logic " + logic
					+ " not supported");
		}
	}

	@Override
	public void setLogic(final Logics logic) throws UnsupportedOperationException {
		if (mTheory != null) {
			throw new SMTLIBException("Logic already set!");
		}
		mTheory = new Theory(logic, mSolverSetup);
	}

	@Override
	public void setOption(final String opt, final Object value)
		throws UnsupportedOperationException, SMTLIBException {
		// Nothing to do
	}

	@Override
	public void setInfo(final String info, final Object value) {
		// Nothing to do
	}

	@Override
	public FunctionSymbol getFunctionSymbol(final String constructor) {
		return mTheory.getFunctionSymbol(constructor);
	}

	@Override
	public DataType.Constructor constructor(final String name, final String[] selectors, final Sort[] argumentSorts) {
		if (name == null) {
			throw new SMTLIBException(
					"Invalid input to declare a datatype");
		}
		checkSymbol(name);
		return mTheory.createConstructor(name, selectors, argumentSorts);
	}

	@Override
	public DataType datatype(final String typename, final int numParams) {
		if (typename == null) {
			throw new SMTLIBException(
					"Invalid input to declare a datatype");
		}
		checkSymbol(typename);
		return mTheory.createDatatypes(typename, numParams);
	}

	/**
	 * Declare internal functions for the constructors and selectors of the datatype.
	 * @param datatype The datatype.
	 * @param constrs The constructors.
	 * @throws SMTLIBException
	 */
	private void declareConstructorFunctions(final DataType datatype, final DataType.Constructor[] constrs, final Sort[] sortParams) {
		final String[] indices = null;
		Sort datatypeSort;
		if (sortParams == null) {
			if (datatype.mNumParams != 0) {
				throw new SMTLIBException("Sort parameters missing");
			}
			datatypeSort = datatype.getSort(indices, Theory.EMPTY_SORT_ARRAY);
		} else {
			if (datatype.mNumParams == 0 || datatype.mNumParams != sortParams.length) {
				throw new SMTLIBException("Sort parameter mismatch");
			}
			datatypeSort = datatype.getSort(indices, sortParams);
		}
		final Sort[] selectorParamSorts = new Sort[] { datatypeSort };

		for (final Constructor cons : constrs) {

			final String constrName = cons.getName();
			final String[] selectors = cons.getSelectors();
			final Sort[] argumentSorts = cons.getArgumentSorts();

			if (sortParams == null) {
				getTheory().declareInternalFunction(constrName, argumentSorts, datatypeSort, FunctionSymbol.CONSTRUCTOR);

				for (int j = 0; j < selectors.length; j++) {
					getTheory().declareInternalFunction(selectors[j], selectorParamSorts, argumentSorts[j], FunctionSymbol.SELECTOR);
				}
			} else {
				final int constrFlags = FunctionSymbol.CONSTRUCTOR
						+ (cons.needsReturnOverload() ? FunctionSymbol.RETURNOVERLOAD : 0);
				getTheory().declareInternalPolymorphicFunction(constrName, sortParams, argumentSorts,
						datatypeSort, constrFlags);

				for (int j = 0; j < selectors.length; j++) {
					getTheory().declareInternalPolymorphicFunction(selectors[j], sortParams, selectorParamSorts,
							argumentSorts[j], FunctionSymbol.SELECTOR);
				}
			}
		}
	}

	@Override
	public void declareDatatype(final DataType datatype, final DataType.Constructor[] constrs) {
		assert datatype.mNumParams == 0;
		datatype.setConstructors(new Sort[0], constrs);
		declareConstructorFunctions(datatype, constrs, null);
	}

	@Override
	public void declareDatatypes(final DataType[] datatypes, final DataType.Constructor[][] constrs, final Sort[][] sortParams) {
		for (int i = 0; i < datatypes.length; i++) {
			datatypes[i].setConstructors(sortParams[i], constrs[i]);
			declareConstructorFunctions(datatypes[i], constrs[i], sortParams[i]);
		}
	}

	@Override
	public void declareSort(final String sort, final int arity) throws SMTLIBException {
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
	public void defineSort(final String sort, final Sort[] sortParams, final Sort definition)
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
	public void declareFun(final String fun, final Sort[] paramSorts, final Sort resultSort)
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
	public void defineFun(final String fun, final TermVariable[] params,
			final Sort resultSort, final Term definition) throws SMTLIBException {
		checkSymbol(fun);
		defineFunInternal(fun, params, resultSort, definition);
	}

	private void defineFunInternal(final String fun, final TermVariable[] params,
			final Sort resultSort, final Term definition) throws SMTLIBException {
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
	public void push(final int levels) {
		if (mTheory == null) {
			throw new SMTLIBException("No logic set!");
		}
		mStackLevel += levels;
		for (int i = 0; i < levels; i++) {
			mTheory.push();
		}
	}

	@Override
	public void pop(final int levels) throws SMTLIBException {
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
	public LBool assertTerm(final Term term) throws SMTLIBException {
		return LBool.UNKNOWN;
	}

	@Override
	public LBool checkSat() {
		return LBool.UNKNOWN;
	}

	@Override
	public LBool checkSatAssuming(final Term... assumptions) {
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
	public Map<Term, Term> getValue(final Term[] terms) throws SMTLIBException,
			UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public Assignments getAssignment() throws SMTLIBException,
			UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public Object getOption(final String opt)
		throws UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public Object getInfo(final String info)
		throws UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public Term simplify(final Term term) throws SMTLIBException {
		throw new UnsupportedOperationException();
	}

	@Override
	public void reset() {
		mTheory = null;
		mStackLevel = 0;
	}

	@Override
	public Term[] getInterpolants(final Term[] partition) throws SMTLIBException,
			UnsupportedOperationException {
		// The default startOfSubtrees is an array with 0's.
		final int[] startOfSubtrees = new int[partition.length];
		return getInterpolants(partition, startOfSubtrees);
	}

	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree)
		throws SMTLIBException, UnsupportedOperationException {
		return getInterpolants(partition, startOfSubtree, getProof());
	}

	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree, final Term proofTree)
			throws SMTLIBException, UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public void exit() {
		// Nothing to do
	}

	@Override
	public Sort sort(final String sortname, final Sort... params) throws SMTLIBException {
		return sort(sortname, null, params);
	}

	@Override
	public Sort sort(final String sortname, final String[] indices, final Sort... params)
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
	public Term term(final String funcname, final Term... params) throws SMTLIBException {
		return term(funcname, null, null, params);
	}

	@Override
	public Term term(final String funcname, final String[] indices,
			final Sort returnSort, final Term... params) throws SMTLIBException {
		if (mTheory == null) {
			throw new SMTLIBException("No logic set!");
		}
		return mTheory.term(funcname, indices, returnSort, params);
	}

	@Override
	public TermVariable variable(final String varname, final Sort sort)
		throws SMTLIBException {
		if (sort == null || varname == null) {
			throw new SMTLIBException(
					"Invalid input to create a term variable");
		}
		checkSymbol(varname);
		return mTheory.createTermVariable(varname, sort);
	}

	@Override
	public Term quantifier(final int quantor, final TermVariable[] vars, Term body,
			final Term[]... patterns) throws SMTLIBException {
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
	public Term let(final TermVariable[] vars, final Term[] values, final Term body)
		throws SMTLIBException {
		if (vars.length != values.length) {
			throw new SMTLIBException(
					"Need exactly one value for every variable");
		}
		return mTheory.let(vars, values, body);
	}

	@Override
	public Term match(final Term dataArg, final TermVariable[][] vars, final Term[] cases,
			final DataType.Constructor[] constructors) throws SMTLIBException {
		return mTheory.match(dataArg, vars, cases, constructors);
	}



	@Override
	public Term annotate(final Term t, final Annotation... annotations)
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
	public Term numeral(final String num) throws SMTLIBException {
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
	public Term numeral(final BigInteger num) throws SMTLIBException {
		if (mTheory == null) {
			throw new SMTLIBException("No logic set!");
		}
		if (mTheory.getNumericSort() == null) {
			throw new SMTLIBException("Logic does not allow numerals");
		}
		return mTheory.numeral(num);
	}

	@Override
	public Term decimal(final String decimal) throws SMTLIBException {
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
	public Term decimal(final BigDecimal decimal) throws SMTLIBException {
		if (mTheory == null) {
			throw new SMTLIBException("No logic set!");
		}
		if (mTheory.getRealSort() == null) {
			throw new SMTLIBException("Logic does not allow reals");
		}
		return mTheory.decimal(decimal);
	}

	@Override
	public Term string(final QuotedObject str) throws SMTLIBException {
		if (mTheory == null) {
			throw new SMTLIBException("No logic set!");
		}
		if (mTheory.getStringSort() == null) {
			throw new SMTLIBException("Logic does not allow strings");
		}
		return mTheory.string(str);
	}

	@Override
	public Term hexadecimal(final String hex) throws SMTLIBException {
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
	public Term binary(final String bin) throws SMTLIBException {
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
	public Sort[] sortVariables(final String... names) throws SMTLIBException {
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
	public Iterable<Term[]> checkAllsat(final Term[] predicates)
		throws SMTLIBException,	UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public Term[] findImpliedEquality(final Term[] x, final Term[] y)
		throws SMTLIBException,	UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public QuotedObject echo(final QuotedObject msg) {
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
