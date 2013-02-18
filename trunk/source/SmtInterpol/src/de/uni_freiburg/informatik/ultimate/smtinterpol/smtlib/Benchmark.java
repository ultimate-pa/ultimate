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
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class Benchmark {
	
	private Script m_Script;
	private int m_FormulaNum;
	private final Map<String, Sort> m_SortTranslator;
	private final Map<String, String> m_FunNameTranslator;
	
	public Benchmark(Script solver, boolean disableIPol) {
		m_Script = solver;
		m_FormulaNum = disableIPol ? -2 : -1;
		m_SortTranslator = new HashMap<String, Sort>();
		m_FunNameTranslator = new HashMap<String, String>();
		m_Script.setOption(":produce-proofs", true);
	}
	
	public void setOption(String option, Object value) {
		m_Script.setOption(option, value);
	}
	
	public void note(String s) {
		if ("Interpolation Problem starts here".equals(s))
			++m_FormulaNum;
	}

	private final void mapFuns() {
		// some benchmarks use abs/mod/div as uninterpreted functions.
		// in smtlib2 they are predefined.  We rename the functions to save 
		// names.
		m_FunNameTranslator.put("abs", "abs$");
		m_FunNameTranslator.put("mod", "mod$");
		m_FunNameTranslator.put("div", "div$");
	}
	
	private final void mapArith() {
		// smtlib1 used ~ for unary minus.
		m_FunNameTranslator.put("~", "-");
	}
	
	private final String translateFunName(String funname) {
		String res = m_FunNameTranslator.get(funname);
		return res == null ? funname : res;
	}
	
	public void setLogic(String logic) {
		Logics l = Logics.valueOf(logic);
		m_Script.setLogic(l);
		switch (l) {
		case QF_AX:
			m_Script.declareSort("Index", 0);
			m_Script.declareSort("Element", 0);
			m_SortTranslator.put("Array",
					m_Script.sort("Array", m_Script.sort("Index"),
							m_Script.sort("Element")));
			break;
		case AUFLIRA:
		case AUFNIRA:
			Sort array1 = m_Script.sort("Array", m_Script.sort("Int"),
					m_Script.sort("Real"));
			m_SortTranslator.put("Array1", array1);
			m_SortTranslator.put("Array2", m_Script.sort("Array", 
					m_Script.sort("Int"), array1));
			mapFuns();
			mapArith();
			break;
		case QF_AUFLIA:
		case AUFLIA:
			m_SortTranslator.put("Array", m_Script.sort("Array",
					m_Script.sort("Int"), m_Script.sort("Real")));
		case QF_UFLIA:
		case QF_UFLRA:
			mapFuns();
			mapArith();
			break;
		case QF_UF:
			m_Script.declareSort("U", 0);
			break;
		case LRA:
		case QF_LIA:
		case QF_LRA:
		case QF_RDL:
		case QF_IDL:
			mapArith();
			break;
		default:
			break;
		}
	}
	
	public void setInfo(String info, String value) {
		m_Script.setInfo(info, value);
	}
	
	public void declareSort(String name) {
		m_Script.declareSort(name, 0);
	}

	public void declareFun(String name, Sort[] paramSorts, Sort resultSort) {
		m_Script.declareFun(translateFunName(name), paramSorts, resultSort);
	}
	
	public Term term(String name, Term... params) {
		return m_Script.term(translateFunName(name), params);
	}
	public Term annotateTerm(Term t, Annotation... annots) {
		if (annots.length > 0)
			t = m_Script.annotate(t, annots);
		return t;
	}
	public Term quantifier(int quantor, TermVariable[] vars, Term body, 
			Term[]...patterns) {
		return m_Script.quantifier(quantor, vars, body, patterns);
	}
	public Term let(TermVariable var, Term value, Term body) {
		return m_Script.let(new TermVariable[]{var}, new Term[]{value}, body);
	}
	public Sort sort(String name) {
		Sort res = m_SortTranslator.get(name);
		if (res != null)
			return res;
		return m_Script.sort(name);
	}
	public TermVariable variable(String name, Sort sort) {
		return m_Script.variable(name, sort);
	}
	public Sort getBooleanSort() {
		return m_Script.sort("Bool");
	}
	public void assertTerm(Term t) {
		if (m_FormulaNum >= 0)
			t = m_Script.annotate(t,
					new Annotation(":named", "IP_" + m_FormulaNum++));
		m_Script.assertTerm(t);
	}
	public Term numeral(String num) {
		return m_Script.numeral(num);
	}
	public Term decimal(String decimal) {
		return m_Script.decimal(decimal);
	}
	public Term[] check() {
		LBool res = m_Script.checkSat();
		if (!(m_Script instanceof LoggingScript))
			System.out.println(res);
		if (m_FormulaNum > 1) {
			Term[] partition = new Term[m_FormulaNum];
			for (int i = 0; i < m_FormulaNum; ++i)
				partition[i] = m_Script.term("IP_" + i);
			return m_Script.getInterpolants(partition);
		}
		return null;
	}
	public void close() {
		m_Script.exit();
	}

	public void getProof() {
		m_Script.getProof();
	}
}
