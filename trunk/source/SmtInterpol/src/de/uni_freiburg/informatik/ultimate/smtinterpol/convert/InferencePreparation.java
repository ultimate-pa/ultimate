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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet.UnletType;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.CollectionsHelper;


public class InferencePreparation {
	private Theory m_theory;
	private Set<TermVariable> m_vars;
	private Stack<Term> m_boolTerms;
	private Term m_subst;
	private ApplicationTerm m_ite;
	
	public InferencePreparation(Theory theory,Set<TermVariable> vars) {
		m_theory = theory;
		m_vars = vars;
		m_boolTerms = new Stack<Term>();
	}
	public Term prepare(Term in) {
		assert in.getSort() == m_theory.getBooleanSort() : 
			"Non-boolean term as quantifier sub?";
		FormulaUnLet unflet = new FormulaUnLet(UnletType.EXPAND_DEFINITIONS);
		return recprepare(unflet.unlet(in));
	}
	
	private Term recprepare(Term in) {
		if (!CollectionsHelper.containsAny(in.getFreeVars(), m_vars))
			return in;
		while (in instanceof AnnotatedTerm)
			in = ((AnnotatedTerm)in).getSubterm();
		if (in instanceof ApplicationTerm) {
			ApplicationTerm app = (ApplicationTerm)in;
			if (app.getSort() == m_theory.getBooleanSort()) {
				m_boolTerms.push(in);
			} else if (app.getFunction().isIntern() && 
					app.getFunction().getName().equals("ite")) {
				// Here, we have a term-ite...
				m_subst = m_ite = app;
				return null;
			}
			Term[] params = app.getParameters();
			Term[] newparams = new Term[params.length];
			for (int i = 0; i < params.length; ++i) {
				newparams[i] = recprepare(params[i]);
				while (newparams[i] == null) {
					// Found term ite in parameter i
					// TODO This does not work: (and p q) vs. (p (f...))
					if (m_boolTerms.peek() != in)
						return null;
					if (m_boolTerms.peek() == in) {
						m_boolTerms.pop();
						return recprepare(generateIte(in));
					}
				}
			}
			if (m_boolTerms.peek() == in)
				m_boolTerms.pop();
			return m_theory.term(app.getFunction(), newparams);
		}
		return in;
	}
	private Term generateIte(Term in) {
		Term trueCase = generateCase(in,true);
		Term falseCase = generateCase(in,false);
		Term res = m_theory.ifthenelse(m_ite.getParameters()[0], trueCase, falseCase);
		m_ite = null; 
		m_subst = null;
		return res;
	}
	private Term generateCase(Term in,boolean which) {
		while (in instanceof AnnotatedTerm)
			in = ((AnnotatedTerm)in).getSubterm();
		if (in == m_subst)
			return m_ite.getParameters()[which ? 1 : 2];
		if (in instanceof ApplicationTerm) {
			ApplicationTerm at = (ApplicationTerm)in;
			Term[] params = at.getParameters();
			Term[] newparams = new Term[params.length];
			boolean changed = false;
			for (int i = 0; i < params.length; ++i) {
				newparams[i] = generateCase(params[i], which);
				changed |= params[i] != newparams[i];
			}
			return changed ? m_theory.term(at.getFunction(),newparams) : at;	
		}
		return in;
	}
	
}
