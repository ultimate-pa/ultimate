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
	
	private final Script m_Script;
	
	

	public ScriptWithTermConstructionChecks(Script script) {
		super();
		m_Script = script;
	}



	public void setLogic(String logic) throws UnsupportedOperationException,
			SMTLIBException {
		m_Script.setLogic(logic);
	}



	public void setLogic(Logics logic) throws UnsupportedOperationException,
			SMTLIBException {
		m_Script.setLogic(logic);
	}



	public void setOption(String opt, Object value)
			throws UnsupportedOperationException, SMTLIBException {
		m_Script.setOption(opt, value);
	}



	public void setInfo(String info, Object value) {
		m_Script.setInfo(info, value);
	}



	public void declareSort(String sort, int arity) throws SMTLIBException {
		m_Script.declareSort(sort, arity);
	}



	public void defineSort(String sort, Sort[] sortParams, Sort definition)
			throws SMTLIBException {
		m_Script.defineSort(sort, sortParams, definition);
	}



	public void declareFun(String fun, Sort[] paramSorts, Sort resultSort)
			throws SMTLIBException {
		m_Script.declareFun(fun, paramSorts, resultSort);
	}



	public void defineFun(String fun, TermVariable[] params, Sort resultSort,
			Term definition) throws SMTLIBException {
		m_Script.defineFun(fun, params, resultSort, definition);
	}



	public void push(int levels) throws SMTLIBException {
		m_Script.push(levels);
	}



	public void pop(int levels) throws SMTLIBException {
		m_Script.pop(levels);
	}



	public LBool assertTerm(Term term) throws SMTLIBException {
		return m_Script.assertTerm(term);
	}



	public LBool checkSat() throws SMTLIBException {
		return m_Script.checkSat();
	}



	public Term[] getAssertions() throws SMTLIBException {
		return m_Script.getAssertions();
	}



	public Term getProof() throws SMTLIBException,
			UnsupportedOperationException {
		return m_Script.getProof();
	}



	public Term[] getUnsatCore() throws SMTLIBException,
			UnsupportedOperationException {
		return m_Script.getUnsatCore();
	}



	public Map<Term, Term> getValue(Term[] terms) throws SMTLIBException,
			UnsupportedOperationException {
		return m_Script.getValue(terms);
	}



	public Assignments getAssignment() throws SMTLIBException,
			UnsupportedOperationException {
		return m_Script.getAssignment();
	}



	public Object getOption(String opt) throws UnsupportedOperationException {
		return m_Script.getOption(opt);
	}



	public Object getInfo(String info) throws UnsupportedOperationException,
			SMTLIBException {
		return m_Script.getInfo(info);
	}



	public void exit() {
		m_Script.exit();
	}



	public Sort sort(String sortname, Sort... params) throws SMTLIBException {
		return m_Script.sort(sortname, params);
	}



	public Sort sort(String sortname, BigInteger[] indices, Sort... params)
			throws SMTLIBException {
		return m_Script.sort(sortname, indices, params);
	}



	public Sort[] sortVariables(String... names) throws SMTLIBException {
		return m_Script.sortVariables(names);
	}



	public Term term(String funcname, Term... params) throws SMTLIBException {
		checkIfsomeParamUsesDifferentTheory(params);
		return m_Script.term(funcname, params);
	}



	private void checkIfsomeParamUsesDifferentTheory(Term[] params) {
		for (Term param : params) {
			Theory paramTheory = getTheory(param);
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
		return m_Script.sort("Bool").getTheory();
	}



	public Term term(String funcname, BigInteger[] indices, Sort returnSort,
			Term... params) throws SMTLIBException {
		checkIfsomeParamUsesDifferentTheory(params);
		return m_Script.term(funcname, indices, returnSort, params);
	}



	public TermVariable variable(String varname, Sort sort)
			throws SMTLIBException {
		return m_Script.variable(varname, sort);
	}



	public Term quantifier(int quantor, TermVariable[] vars, Term body,
			Term[]... patterns) throws SMTLIBException {
		return m_Script.quantifier(quantor, vars, body, patterns);
	}



	public Term let(TermVariable[] vars, Term[] values, Term body)
			throws SMTLIBException {
		return m_Script.let(vars, values, body);
	}



	public Term annotate(Term t, Annotation... annotations)
			throws SMTLIBException {
		return m_Script.annotate(t, annotations);
	}



	public Term numeral(String num) throws SMTLIBException {
		return m_Script.numeral(num);
	}



	public Term numeral(BigInteger num) throws SMTLIBException {
		return m_Script.numeral(num);
	}



	public Term decimal(String decimal) throws SMTLIBException {
		return m_Script.decimal(decimal);
	}



	public Term decimal(BigDecimal decimal) throws SMTLIBException {
		return m_Script.decimal(decimal);
	}



	public Term hexadecimal(String hex) throws SMTLIBException {
		return m_Script.hexadecimal(hex);
	}



	public Term binary(String bin) throws SMTLIBException {
		return m_Script.binary(bin);
	}



	public Term string(String str) throws SMTLIBException {
		return m_Script.string(str);
	}



	public Term simplify(Term term) throws SMTLIBException {
		return m_Script.simplify(term);
	}



	public void reset() {
		m_Script.reset();
	}



	public Term[] getInterpolants(Term[] partition) throws SMTLIBException,
			UnsupportedOperationException {
		return m_Script.getInterpolants(partition);
	}



	public Term[] getInterpolants(Term[] partition, int[] startOfSubtree)
			throws SMTLIBException, UnsupportedOperationException {
		return m_Script.getInterpolants(partition, startOfSubtree);
	}



	public Model getModel() throws SMTLIBException,
			UnsupportedOperationException {
		return m_Script.getModel();
	}



	public Iterable<Term[]> checkAllsat(Term[] predicates)
			throws SMTLIBException, UnsupportedOperationException {
		return m_Script.checkAllsat(predicates);
	}



	public Term[] findImpliedEquality(Term[] x, Term[] y) {
		return m_Script.findImpliedEquality(x, y);
	}



	public QuotedObject echo(QuotedObject msg) {
		return m_Script.echo(msg);
	}
	
	



}
