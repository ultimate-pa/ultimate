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
	
	private final static TermVariable[] EMPTY_TVAR_ARRAY = new TermVariable[0];
	
	private Theory m_Theory;
	protected int m_StackLevel = 0;
	
	protected SolverSetup m_SolverSetup;
	
	public NoopScript() {
		this(null, null);
	}
	
	protected NoopScript(Theory theory) {
		this(theory, null);
	}
	
	protected NoopScript(Theory theory, SolverSetup setup){
		m_Theory = theory;
		m_SolverSetup = setup;
	}
	
	public Theory getTheory() {
		return m_Theory;
	}	
	
	@Override
	public void setLogic(String logic) throws UnsupportedOperationException {
		try {
			setLogic(Logics.valueOf(logic));
		} catch (IllegalArgumentException logicUnsupported) {
			/* Logic is not in enumeration */
			throw new UnsupportedOperationException("Logic " + logic + 
					" not supported");
		}
	}
	
	@Override
	public void setLogic(Logics logic) throws UnsupportedOperationException {
		if (m_Theory != null)
			throw new SMTLIBException("Logic already set!");
		m_Theory = new Theory(logic, m_SolverSetup);
	}

	@Override
	public void setOption(String opt, Object value)
			throws UnsupportedOperationException, SMTLIBException {}

	@Override
	public void setInfo(String info, Object value) {}

	@Override
	public void declareSort(String sort, int arity) throws SMTLIBException {
		if (m_Theory == null)
			throw new SMTLIBException("No logic set!");
		try {
			m_Theory.declareSort(sort, arity);
		} catch (IllegalArgumentException iae) {
			throw new SMTLIBException(iae.getMessage());
		}
	}

	@Override
	public void defineSort(String sort, Sort[] sortParams, Sort definition)
			throws SMTLIBException {
		if (m_Theory == null)
			throw new SMTLIBException("No logic set!");
		try {
			m_Theory.defineSort(sort, sortParams.length, definition);
		} catch (IllegalArgumentException iae) {
			throw new SMTLIBException(iae.getMessage());
		}
	}

	@Override
	public void declareFun(String fun, Sort[] paramSorts, Sort resultSort)
			throws SMTLIBException {
		if (m_Theory == null)
			throw new SMTLIBException("No logic set!");
		try {
			m_Theory.declareFunction(fun, paramSorts, resultSort);
		} catch (IllegalArgumentException iae) {
			throw new SMTLIBException(iae.getMessage());
		}
	}

	@Override
	public void defineFun(String fun, TermVariable[] params,
			Sort resultSort, Term definition) throws SMTLIBException {
		defineFunInternal(fun, params, resultSort, definition);
	}
	
	private void defineFunInternal(String fun, TermVariable[] params,
			Sort resultSort, Term definition) throws SMTLIBException {
		if (m_Theory == null)
			throw new SMTLIBException("No logic set!");
        if (!resultSort.equals(definition.getSort()))
        	throw new SMTLIBException("Sort mismatch");
        try {
        	m_Theory.defineFunction(fun, params, definition);
        } catch (IllegalArgumentException iae) {
        	throw new SMTLIBException(iae.getMessage());
        }
	}

	@Override
	public void push(int levels) {
		if (m_Theory == null)
			throw new SMTLIBException("No logic set!");
		m_StackLevel += levels;
		for (int i = 0; i < levels; i++)
			m_Theory.push();
	}

	@Override
	public void pop(int levels) throws SMTLIBException {
		if (m_Theory == null)
			throw new SMTLIBException("No logic set!");
		if (levels > m_StackLevel)
			throw new SMTLIBException("Not enough levels on assertion stack");
		m_StackLevel -= levels;
		for (int i = 0; i < levels; i++)
			m_Theory.pop();
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
		m_Theory = null;
        m_StackLevel = 0;
	}

	@Override
	public Term[] getInterpolants(Term[] partition) throws SMTLIBException,
			UnsupportedOperationException {
		// The default startOfSubtrees is an array with 0's.
		int[] startOfSubtrees = new int[partition.length];
		return getInterpolants(partition, startOfSubtrees);
	}

	@Override
	public Term[] getInterpolants(Term[] partition, int[] startOfSubtree)
	throws SMTLIBException, UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public void exit() {}

	@Override
	public Sort sort(String sortname, Sort... params) throws SMTLIBException {
		return sort(sortname, null, params);
	}

	@Override
	public Sort sort(String sortname, BigInteger[] indices, Sort... params)
	throws SMTLIBException {
		if (m_Theory == null)
			throw new SMTLIBException("No logic set!");
		Sort res = m_Theory.getSort(sortname, indices, params);
		if (res == null)
			throw new SMTLIBException("Sort " + sortname + " not declared");
		return res;
	}

	@Override
	public Term term(String funcname, Term... params) throws SMTLIBException {
		return term(funcname, null, null, params);
	}

	@Override
	public Term term(String funcname, BigInteger[] indices,
			Sort returnSort, Term... params) throws SMTLIBException {
		if (m_Theory == null)
			throw new SMTLIBException("No logic set!");
		Sort[] sorts = new Sort[params.length];
		for (int i = 0; i < sorts.length; i++) {
			sorts[i] = params[i].getSort();
		}
		FunctionSymbol fsym = m_Theory
				.getFunctionWithResult(funcname, indices, returnSort, sorts);
		//TODO: remove once everything is non-recursive.
		// JC: Commented out for a try-run
//		if (fsym == m_Theory.m_And
//			|| fsym == m_Theory.m_Or)
//			return flattenAndOr(fsym, params);
		if (fsym == null) {
			StringBuilder sb = new StringBuilder();
			PrintTerm pt = new PrintTerm();
			sb.append("Undeclared function symbol (").append(funcname);
			for (Sort s: sorts) {
				sb.append(" ");
				pt.append(sb, s);
			}
			sb.append(")");
			throw new SMTLIBException(sb.toString());
		}
		return m_Theory.term(fsym, params);
	}
	
	private Term flattenAndOr(FunctionSymbol connector, Term[] subforms)
	{
		ArrayList<Term> formulas = new ArrayList<Term>();
		/* Normalize nested and/ors */
		for (Term f : subforms) {
			if (f instanceof ApplicationTerm
				&& ((ApplicationTerm) f).getFunction() == connector) {
				for (Term subf : ((ApplicationTerm) f).getParameters())
					formulas.add(subf);
			} else  {
				formulas.add(f);
			}
		}
		Term[] arrforms = formulas.toArray(new Term[formulas.size()]);
		return m_Theory.term(connector, arrforms);
	}

	@Override
	public TermVariable variable(String varname, Sort sort)
	throws SMTLIBException {
		if (sort == null || varname == null)
			throw new SMTLIBException("Invalid input to create a term variable");
		return m_Theory.createTermVariable(varname, sort);
	}

	@Override
	public Term quantifier(int quantor, TermVariable[] vars, Term body,
			Term[]... patterns) throws SMTLIBException {
		if (!m_Theory.getLogic().isQuantified())
			throw new SMTLIBException(
					"Cannot create quantifier in quantifier-free logic");
		if (vars.length == 0)
			throw new SMTLIBException("No quantified variables given");
		if (body == null)
			throw new SMTLIBException("Empty quantifier body");
		if (patterns != null && patterns.length > 0) {
	  		Annotation[] annots = new Annotation[patterns.length];
	  		int i = 0;
	  		for (Term[] p : patterns) {
	  			annots[i++] = new Annotation(":pattern", p);
	  		}
	  		body = m_Theory.annotatedTerm(annots, body);
		}
		if (quantor == Script.EXISTS)
			return m_Theory.exists(vars, body);
		if (quantor == Script.FORALL)
			return m_Theory.forall(vars, body);
		throw new SMTLIBException("Unknown Quantifier");
	}

	@Override
	public Term let(TermVariable[] vars, Term[] values, Term body)
	throws SMTLIBException {
		if (vars.length != values.length)
			throw new SMTLIBException(
					"Need exactly one value for every variable");
		return m_Theory.let(vars, values, body);
	}

	@Override
	public Term annotate(Term t, Annotation... annotations)
			throws SMTLIBException {
		if (annotations.length > 0) {
  			for (Annotation a : annotations) {
  			    if (a.getKey().equals(":named")) {
  			    	if (!(a.getValue() instanceof String))
  			    		throw new SMTLIBException(
  			    				"Need a string value for :named");
  			    	if (t.getFreeVars().length != 0)
  			    		throw new SMTLIBException("Cannot name open terms");
  			    	else
  			    	    defineFunInternal((String) a.getValue(), 
  			    	    	EMPTY_TVAR_ARRAY, t.getSort(), t);
  			    }
  			}
  			return m_Theory.annotatedTerm(annotations, t);
  		} else {
  			return t;
  		}
	}

	@Override
	public Term numeral(String num) throws SMTLIBException {
		if (m_Theory == null)
			throw new SMTLIBException("No logic set!");
		if (m_Theory.getNumericSort() == null)
			throw new SMTLIBException("Logic does not allow numerals");
		try {
			return m_Theory.numeral(num);
		} catch (NumberFormatException noname) {
			throw new SMTLIBException("Not a numeral: " + num);
		}
	}
	
	@Override
	public Term numeral(BigInteger num) throws SMTLIBException {
		if (m_Theory == null)
			throw new SMTLIBException("No logic set!");
		if (m_Theory.getNumericSort() == null)
			throw new SMTLIBException("Logic does not allow numerals");
		return m_Theory.numeral(num);
	}

	@Override
	public Term decimal(String decimal) throws SMTLIBException {
		if (m_Theory == null)
			throw new SMTLIBException("No logic set!");
		if (m_Theory.getRealSort() == null)
			throw new SMTLIBException("Logic does not allow reals");
		try {
			return m_Theory.decimal(decimal);
		} catch (NumberFormatException noname) {
			throw new SMTLIBException("Not a decimal: " + decimal);
		}
	}

	@Override
	public Term decimal(BigDecimal decimal) throws SMTLIBException {
		if (m_Theory == null)
			throw new SMTLIBException("No logic set!");
		if (m_Theory.getRealSort() == null)
			throw new SMTLIBException("Logic does not allow reals");
		return m_Theory.decimal(decimal);
	}

	@Override
	public Term string(String str) throws SMTLIBException {
		if (m_Theory == null)
			throw new SMTLIBException("No logic set!");
		if (m_Theory.getStringSort() == null)
			throw new SMTLIBException("Logic does not allow strings");
		return m_Theory.string(str);
	}

	@Override
	public Term hexadecimal(String hex) throws SMTLIBException {
		if (m_Theory == null)
			throw new SMTLIBException("No logic set!");
		Term res = m_Theory.hexadecimal(hex);
		if (res == null)
			throw new SMTLIBException("No bitvector logic");
		return res;
	}

	@Override
	public Term binary(String bin) throws SMTLIBException {
		if (m_Theory == null)
			throw new SMTLIBException("No logic set!");
		Term res = m_Theory.binary(bin);
		if (res == null)
			throw new SMTLIBException("No bitvector logic");
		return res;
	}
		
	@Override
	public Sort[] sortVariables(String... names) throws SMTLIBException {
		if (m_Theory == null)
			throw new SMTLIBException("No logic set!");
		return m_Theory.createSortVariables(names);
	}
	
	@Override
	public Model getModel() throws SMTLIBException,
			UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterable<Term[]> checkAllsat(Term[] predicates) throws SMTLIBException,
			UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}		

}
