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

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.QuantifiedAtom;


public class ForallFormula extends FlatFormula {
	Term smtFormula;
	QuantifiedAtom lit;
	NegForallFormula negated;
	Set<TermVariable> vars;
	Term[][] triggers;
	Term subformula;
	boolean auxAxiomsAdded;
	Set<TermVariable> freeVars;
	Map<TermVariable, FlatTerm> letTable;
	TriggerData[] trigData;
	InstantiationUnifier iu;
	
	public ForallFormula(ConvertFormula converter, Term smtForm,
			Set<TermVariable> vars, Term[][] trigs, Term subform) {
		super(converter);
		this.smtFormula = smtForm;
		this.vars = vars;
		this.negated = new NegForallFormula(this);
		this.triggers = trigs;
		this.subformula = subform;
		freeVars = null;
		letTable = new HashMap<TermVariable, FlatTerm>(converter.letTable);
		trigData = null;
		this.iu = new InstantiationUnifier(vars);
	}
	
	public FlatFormula negate() {
		return negated;
	}
	
	public void addAuxAxioms() {
		m_converter.dpllEngine.setCompleteness(DPLLEngine.INCOMPLETE_QUANTIFIER);
		if (triggers != null) {
			compileTrigger();
			((QuantifiedAtom)lit).setTriggers(trigData);
			for (TriggerData td : trigData)
				td.yieldTrigger.setProxyLiteral(lit);
		}
		auxAxiomsAdded = true;
	}

	public void addAsAxiom(ClauseDeletionHook hook) {
		m_converter.dpllEngine.setCompleteness(DPLLEngine.INCOMPLETE_QUANTIFIER);
		if (triggers != null) {
			compileTrigger();
			for (TriggerData td : trigData)
				m_converter.quantTheory.add(td);
		}
	}
	
	public Term getSMTTerm(boolean useAuxVars) {
		return smtFormula;
	}

	public Literal getLiteral() {
		if (lit == null) {
			lit = m_converter.createQuantifiedAtom(smtFormula);
			m_converter.m_RemoveLit.add(this);
		}
		if (!auxAxiomsAdded)
			addAuxAxioms();
		return lit;
	}

	public void toStringHelper(StringBuilder sb, HashSet<FlatTerm> visited) {
		sb.append("[").append(hashCode()).append("]");
		if (visited.contains(this))
			return;
		visited.add(this);
		sb.append("(FORALL (");
		String sep = "";
		for (TermVariable v: vars) {
			sb.append(sep).append(v);
			sep = " ";
		}
		sb.append(") ").append(subformula).append(")");
	}
	public Set<TermVariable> getFreeVars() {
		if (freeVars == null) {
			freeVars = new HashSet<TermVariable>();
			for (TermVariable tv : subformula.getFreeVars())
				freeVars.add(tv);
			for (TermVariable tv : vars)
				freeVars.remove(tv);
		}
		return freeVars;
	}
	public void literalRemoved() {
		lit = null;
		trigData = null;
	}
	public Set<FlatFormula> getSubFormulas() {
		return Collections.singleton((FlatFormula) this);
	}
	private void compileTrigger() {
		if (trigData == null) {
			trigData = new TriggerData[triggers.length];
			for (int i = 0; i < triggers.length; ++i) {
				trigData[i] = m_converter.patternCompiler.compile(
						vars,triggers[i],m_converter);
				trigData[i].yieldTrigger.postInit(
						m_converter, letTable, subformula, iu);
			}
		}
	}

	public void intern() {}
	public void accept(FlatTermVisitor visitor) {
		visitor.visit(this);
	}
}
