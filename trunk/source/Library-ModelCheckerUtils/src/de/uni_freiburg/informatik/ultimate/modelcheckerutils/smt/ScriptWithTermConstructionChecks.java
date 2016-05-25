/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * Script that wraps an existing Script but has additional checks for the
 * construction of Terms. Whenever a Term is constructed we check if all
 * params have the same Theory.
 * This is useful to detect the common mistake that Terms are combined that
 * have been constructed using different Scripts. 
 * This is not a perfect solution, should be considered as a workaround and used
 * only for debugging.
 * @author Matthias Heizmann
 */
public class ScriptWithTermConstructionChecks implements Script {
	
	private final Script mScript;
	
	

	public ScriptWithTermConstructionChecks(Script script) {
		super();
		mScript = script;
	}



	@Override
	public void setLogic(String logic) throws UnsupportedOperationException,
			SMTLIBException {
		mScript.setLogic(logic);
	}



	@Override
	public void setLogic(Logics logic) throws UnsupportedOperationException,
			SMTLIBException {
		mScript.setLogic(logic);
	}



	@Override
	public void setOption(String opt, Object value)
			throws UnsupportedOperationException, SMTLIBException {
		mScript.setOption(opt, value);
	}



	@Override
	public void setInfo(String info, Object value) {
		mScript.setInfo(info, value);
	}



	@Override
	public void declareSort(String sort, int arity) throws SMTLIBException {
		mScript.declareSort(sort, arity);
	}



	@Override
	public void defineSort(String sort, Sort[] sortParams, Sort definition)
			throws SMTLIBException {
		mScript.defineSort(sort, sortParams, definition);
	}



	@Override
	public void declareFun(String fun, Sort[] paramSorts, Sort resultSort)
			throws SMTLIBException {
		mScript.declareFun(fun, paramSorts, resultSort);
	}



	@Override
	public void defineFun(String fun, TermVariable[] params, Sort resultSort,
			Term definition) throws SMTLIBException {
		mScript.defineFun(fun, params, resultSort, definition);
	}



	@Override
	public void push(int levels) throws SMTLIBException {
		mScript.push(levels);
	}



	@Override
	public void pop(int levels) throws SMTLIBException {
		mScript.pop(levels);
	}



	@Override
	public LBool assertTerm(Term term) throws SMTLIBException {
		return mScript.assertTerm(term);
	}



	@Override
	public LBool checkSat() throws SMTLIBException {
		return mScript.checkSat();
	}



	@Override
	public Term[] getAssertions() throws SMTLIBException {
		return mScript.getAssertions();
	}



	@Override
	public Term getProof() throws SMTLIBException,
			UnsupportedOperationException {
		return mScript.getProof();
	}



	@Override
	public Term[] getUnsatCore() throws SMTLIBException,
			UnsupportedOperationException {
		return mScript.getUnsatCore();
	}



	@Override
	public Map<Term, Term> getValue(Term[] terms) throws SMTLIBException,
			UnsupportedOperationException {
		return mScript.getValue(terms);
	}



	@Override
	public Assignments getAssignment() throws SMTLIBException,
			UnsupportedOperationException {
		return mScript.getAssignment();
	}



	@Override
	public Object getOption(String opt) throws UnsupportedOperationException {
		return mScript.getOption(opt);
	}



	@Override
	public Object getInfo(String info) throws UnsupportedOperationException,
			SMTLIBException {
		return mScript.getInfo(info);
	}



	@Override
	public void exit() {
		mScript.exit();
	}



	@Override
	public Sort sort(String sortname, Sort... params) throws SMTLIBException {
		return mScript.sort(sortname, params);
	}



	@Override
	public Sort sort(String sortname, BigInteger[] indices, Sort... params)
			throws SMTLIBException {
		return mScript.sort(sortname, indices, params);
	}



	@Override
	public Sort[] sortVariables(String... names) throws SMTLIBException {
		return mScript.sortVariables(names);
	}



	@Override
	public Term term(String funcname, Term... params) throws SMTLIBException {
		checkIfsomeParamUsesDifferentTheory(params);
		return mScript.term(funcname, params);
	}



	private void checkIfsomeParamUsesDifferentTheory(Term[] params) {
		for (final Term param : params) {
			final Theory paramTheory = getTheory(param);
			if (paramTheory != getThisScriptsTheory()) {
				throw new IllegalArgumentException(
						"Param was constructed with different Script: " + param);
			}
		}
	}



	private Theory getTheory(Term param) {
		return param.getSort().getTheory();
	}
	
	private Theory getThisScriptsTheory() {
		return mScript.sort("Bool").getTheory();
	}



	@Override
	public Term term(String funcname, BigInteger[] indices, Sort returnSort,
			Term... params) throws SMTLIBException {
		checkIfsomeParamUsesDifferentTheory(params);
		return mScript.term(funcname, indices, returnSort, params);
	}



	@Override
	public TermVariable variable(String varname, Sort sort)
			throws SMTLIBException {
		return mScript.variable(varname, sort);
	}



	@Override
	public Term quantifier(int quantor, TermVariable[] vars, Term body,
			Term[]... patterns) throws SMTLIBException {
		return mScript.quantifier(quantor, vars, body, patterns);
	}



	@Override
	public Term let(TermVariable[] vars, Term[] values, Term body)
			throws SMTLIBException {
		return mScript.let(vars, values, body);
	}



	@Override
	public Term annotate(Term t, Annotation... annotations)
			throws SMTLIBException {
		return mScript.annotate(t, annotations);
	}



	@Override
	public Term numeral(String num) throws SMTLIBException {
		return mScript.numeral(num);
	}



	@Override
	public Term numeral(BigInteger num) throws SMTLIBException {
		return mScript.numeral(num);
	}



	@Override
	public Term decimal(String decimal) throws SMTLIBException {
		return mScript.decimal(decimal);
	}



	@Override
	public Term decimal(BigDecimal decimal) throws SMTLIBException {
		return mScript.decimal(decimal);
	}



	@Override
	public Term hexadecimal(String hex) throws SMTLIBException {
		return mScript.hexadecimal(hex);
	}



	@Override
	public Term binary(String bin) throws SMTLIBException {
		return mScript.binary(bin);
	}



	@Override
	public Term string(String str) throws SMTLIBException {
		return mScript.string(str);
	}



	@Override
	public Term simplify(Term term) throws SMTLIBException {
		return mScript.simplify(term);
	}



	@Override
	public void reset() {
		mScript.reset();
	}



	@Override
	public Term[] getInterpolants(Term[] partition) throws SMTLIBException,
			UnsupportedOperationException {
		return mScript.getInterpolants(partition);
	}



	@Override
	public Term[] getInterpolants(Term[] partition, int[] startOfSubtree)
			throws SMTLIBException, UnsupportedOperationException {
		return mScript.getInterpolants(partition, startOfSubtree);
	}



	@Override
	public Model getModel() throws SMTLIBException,
			UnsupportedOperationException {
		return mScript.getModel();
	}



	@Override
	public Iterable<Term[]> checkAllsat(Term[] predicates)
			throws SMTLIBException, UnsupportedOperationException {
		return mScript.checkAllsat(predicates);
	}



	@Override
	public Term[] findImpliedEquality(Term[] x, Term[] y) {
		return mScript.findImpliedEquality(x, y);
	}



	@Override
	public QuotedObject echo(QuotedObject msg) {
		return mScript.echo(msg);
	}
	
	



}
