/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.logic;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Iterator;
import java.util.Map;
import java.util.Objects;

/**
 * Base class for implementing wrapping scripts.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class WrapperScript implements Script {

	protected final Script mScript;

	protected WrapperScript(final Script wrappedScript) {
		mScript = Objects.requireNonNull(wrappedScript);
	}

	/**
	 * Find the first {@link Script} instance that has the given type or is a subtype of the given type in the stack of
	 * {@link Script} instances represented by this {@link WrapperScript}.
	 *
	 * @param <T>
	 *            The type of {@link Script} to search for.
	 * @param clazz
	 *            The {@link Class} instance representing the type.
	 * @return A {@link Script} instance if one can be found or null.
	 */
	@SuppressWarnings("unchecked")
	public <T extends Script> T findBacking(final Class<T> clazz) {
		final Iterator<Script> iter = getScriptIterator();
		while (iter.hasNext()) {
			final Script current = iter.next();
			if (clazz.isAssignableFrom(current.getClass())) {
				return (T) current;
			}
		}
		return null;
	}

	/**
	 * @return an {@link Iterator} that iterates over this stack of {@link Script} instances.
	 */
	public Iterator<Script> getScriptIterator() {
		final Script current = this;
		return new Iterator<Script>() {

			private Script mBacking = current;

			@Override
			public boolean hasNext() {
				return mBacking instanceof WrapperScript;
			}

			@Override
			public Script next() {
				final Script rtr = mBacking;
				mBacking = ((WrapperScript) mBacking).mScript;
				return rtr;
			}
		};
	}

	@Override
	public void setLogic(final String logic) throws UnsupportedOperationException, SMTLIBException {
		mScript.setLogic(logic);
	}

	@Override
	public void setLogic(final Logics logic) throws UnsupportedOperationException, SMTLIBException {
		mScript.setLogic(logic);
	}

	@Override
	public void setOption(final String opt, final Object value) throws UnsupportedOperationException, SMTLIBException {
		mScript.setOption(opt, value);
	}

	@Override
	public void setInfo(final String info, final Object value) {
		mScript.setInfo(info, value);
	}

	@Override
	public void declareSort(final String sort, final int arity) throws SMTLIBException {
		mScript.declareSort(sort, arity);
	}

	@Override
	public void defineSort(final String sort, final Sort[] sortParams, final Sort definition) throws SMTLIBException {
		mScript.defineSort(sort, sortParams, definition);
	}

	@Override
	public void declareDatatype(final DataType datatype, final DataType.Constructor[] constrs) throws SMTLIBException {
		mScript.declareDatatype(datatype, constrs);
	}

	@Override
	public void declareDatatypes(final DataType[] datatypes, final DataType.Constructor[][] constrs,
			final Sort[][] sortParams) throws SMTLIBException {
		mScript.declareDatatypes(datatypes, constrs, sortParams);
	}

	@Override
	public void declareFun(final String fun, final Sort[] paramSorts, final Sort resultSort) throws SMTLIBException {
		mScript.declareFun(fun, paramSorts, resultSort);
	}

	@Override
	public void defineFun(final String fun, final TermVariable[] params, final Sort resultSort, final Term definition)
			throws SMTLIBException {
		mScript.defineFun(fun, params, resultSort, definition);
	}

	@Override
	public void push(final int levels) throws SMTLIBException {
		mScript.push(levels);
	}

	@Override
	public void pop(final int levels) throws SMTLIBException {
		mScript.pop(levels);
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		return mScript.assertTerm(term);
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		return mScript.checkSat();
	}

	@Override
	public LBool checkSatAssuming(final Term... assumptions) throws SMTLIBException {
		return mScript.checkSatAssuming(assumptions);
	}

	@Override
	public Term[] getAssertions() throws SMTLIBException {
		return mScript.getAssertions();
	}

	@Override
	public Term getProof() throws SMTLIBException, UnsupportedOperationException {
		return mScript.getProof();
	}

	@Override
	public Term[] getUnsatCore() throws SMTLIBException, UnsupportedOperationException {
		return mScript.getUnsatCore();
	}

	@Override
	public Term[] getUnsatAssumptions() throws SMTLIBException, UnsupportedOperationException {
		return mScript.getUnsatAssumptions();
	}

	@Override
	public Map<Term, Term> getValue(final Term[] terms) throws SMTLIBException, UnsupportedOperationException {
		return mScript.getValue(terms);
	}

	@Override
	public Assignments getAssignment() throws SMTLIBException, UnsupportedOperationException {
		return mScript.getAssignment();
	}

	@Override
	public Object getOption(final String opt) throws UnsupportedOperationException {
		return mScript.getOption(opt);
	}

	@Override
	public Object getInfo(final String info) throws UnsupportedOperationException, SMTLIBException {
		return mScript.getInfo(info);
	}

	@Override
	public void exit() {
		mScript.exit();
	}

	@Override
	public Theory getTheory() {
		return mScript.getTheory();
	}

	@Override
	public Sort sort(final String sortname, final Sort... params) throws SMTLIBException {
		return mScript.sort(sortname, params);
	}

	@Override
	public Sort sort(final String sortname, final String[] indices, final Sort... params) throws SMTLIBException {
		return mScript.sort(sortname, indices, params);
	}

	@Override
	public Sort[] sortVariables(final String... names) throws SMTLIBException {
		return mScript.sortVariables(names);
	}

	@Override
	public DataType.Constructor constructor(final String name, final String[] selectors, final Sort[] argumentSorts)
			throws SMTLIBException {
		return mScript.constructor(name, selectors, argumentSorts);
	}

	@Override
	public DataType datatype(final String typename, final int numParams) throws SMTLIBException {
		return mScript.datatype(typename, numParams);
	}

	@Override
	public Term term(final String funcname, final Term... params) throws SMTLIBException {
		return mScript.term(funcname, params);
	}

	@Override
	public Term term(final String funcname, final String[] indices, final Sort returnSort, final Term... params)
			throws SMTLIBException {
		return mScript.term(funcname, indices, returnSort, params);
	}

	@Override
	public TermVariable variable(final String varname, final Sort sort) throws SMTLIBException {
		return mScript.variable(varname, sort);
	}

	@Override
	public Term quantifier(final int quantor, final TermVariable[] vars, final Term body, final Term[]... patterns)
			throws SMTLIBException {
		return mScript.quantifier(quantor, vars, body, patterns);
	}

	@Override
	public Term let(final TermVariable[] vars, final Term[] values, final Term body) throws SMTLIBException {
		return mScript.let(vars, values, body);
	}

	@Override
	public Term match(final Term dataArg, final TermVariable[][] vars, final Term[] cases,
			final DataType.Constructor[] constructors) throws SMTLIBException {
		return mScript.match(dataArg, vars, cases, constructors);
	}

	@Override
	public Term annotate(final Term t, final Annotation... annotations) throws SMTLIBException {
		return mScript.annotate(t, annotations);
	}

	@Override
	public Term numeral(final String num) throws SMTLIBException {
		return mScript.numeral(num);
	}

	@Override
	public Term numeral(final BigInteger num) throws SMTLIBException {
		return mScript.numeral(num);
	}

	@Override
	public Term decimal(final String decimal) throws SMTLIBException {
		return mScript.decimal(decimal);
	}

	@Override
	public Term decimal(final BigDecimal decimal) throws SMTLIBException {
		return mScript.decimal(decimal);
	}

	@Override
	public Term hexadecimal(final String hex) throws SMTLIBException {
		return mScript.hexadecimal(hex);
	}

	@Override
	public Term binary(final String bin) throws SMTLIBException {
		return mScript.binary(bin);
	}

	@Override
	public Term string(final QuotedObject str) throws SMTLIBException {
		return mScript.string(str);
	}

	@Override
	public Term simplify(final Term term) throws SMTLIBException {
		return mScript.simplify(term);
	}

	@Override
	public void reset() {
		mScript.reset();
	}

	@Override
	public void resetAssertions() {
		mScript.resetAssertions();
	}

	@Override
	public Term[] getInterpolants(final Term[] partition) throws SMTLIBException, UnsupportedOperationException {
		return mScript.getInterpolants(partition);
	}

	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree)
			throws SMTLIBException, UnsupportedOperationException {
		return mScript.getInterpolants(partition, startOfSubtree);
	}

	@Override
	public Model getModel() throws SMTLIBException, UnsupportedOperationException {
		return mScript.getModel();
	}

	@Override
	public Iterable<Term[]> checkAllsat(final Term[] predicates) throws SMTLIBException, UnsupportedOperationException {
		return mScript.checkAllsat(predicates);
	}

	@Override
	public Term[] findImpliedEquality(final Term[] x, final Term[] y) {
		return mScript.findImpliedEquality(x, y);
	}

	@Override
	public QuotedObject echo(final QuotedObject msg) {
		return mScript.echo(msg);
	}

	@Override
	public FunctionSymbol getFunctionSymbol(final String constructor) {
		return mScript.getFunctionSymbol(constructor);
	}

	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree, final Term proofTree)
			throws SMTLIBException, UnsupportedOperationException {
		return mScript.getInterpolants(partition, startOfSubtree, proofTree);
	}

}
