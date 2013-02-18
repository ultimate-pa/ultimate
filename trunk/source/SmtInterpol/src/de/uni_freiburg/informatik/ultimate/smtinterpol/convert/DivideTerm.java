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

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;


/**
 * Represents an integer divide term. The term is the result of an integer
 * division of some affine term with a constant integer.
 * The idea is to create a new integer variable shareddiv
 * representing shared/divisor.  Then we add the constraint
 * <pre>0 &lt;= shared - divisor * shareddiv &lt; divisor</pre>
 * @author hoenicke
 */
public class DivideTerm extends SharedTermOld implements ClauseDeletionHook {
	final AffineTerm m_affineTerm;
	final Rational   m_divisor;
	TermVariable m_auxVar;
	boolean axiomsCreated;
	
	public DivideTerm(AffineTerm affineTerm, Rational divisor) { 
		super(affineTerm.m_converter);
		m_affineTerm = affineTerm;
		m_divisor = divisor;
		assert (divisor.isIntegral() && divisor.signum() != 0);
		assert (affineTerm.isIntegral() || divisor.equals(Rational.ONE));
		axiomsCreated = false;
	}
	
	public void createAxioms() {
		if (axiomsCreated)
			return;
		m_auxVar = m_converter.createAuxVariable(computeTerm());
		AffineTerm negremainder = 
			m_affineTerm.add(new AffineTerm(m_divisor.negate(), this)).negate();
		/* create remainder >= 0  (-remainder <= 0) */
		FlatFormula geqZero = m_converter.createLeq0Formula(negremainder);
		/* create remainder < divisor   not (divisor - remainder <= 0) */
		FlatFormula lessDiv = 
			m_converter.createLeq0Formula(negremainder.add(m_divisor)).negate();
		geqZero.addAsAxiom(this);
		lessDiv.addAsAxiom(this);
		axiomsCreated = true;
	}
	
	@Override
	public Term getSMTTerm(boolean useAuxVars) {
		if (useAuxVars)
			return m_auxVar;
		return computeTerm();
	}
	
	public Term computeTerm() {
		Term smtTerm;
		Term subTerm = m_affineTerm.getSMTTerm();
		Theory t = m_converter.getTheory();
		if (m_affineTerm.isIntegral()) {
			Sort sort = subTerm.getSort();
			smtTerm = t.term(t.getFunction("div", sort, sort), 
					subTerm, t.numeral(m_divisor.numerator()));
		} else {
			assert (m_divisor.equals(Rational.ONE));
			smtTerm = t.term(t.getFunction("to_int", subTerm.getSort()), 
					subTerm);
		}
		return smtTerm;
	}
	
	@Override
	public Sort getSort() {
		return m_converter.getTheory().getSort("Int");
	}

	@Override
	public CCTerm toCCTerm() {
		if (m_ccterm == null) {
//			m_ccterm = m_converter.cclosure.createAnonTerm(this);
			share();
			m_converter.m_UnshareCC.add(this);
		}
		return m_ccterm;
	}
	
	public void toStringHelper(StringBuilder sb, HashSet<FlatTerm> visited) {
		sb.append(getSMTTerm().toString());
	}

	@Override
	public boolean clauseDeleted(Clause c, DPLLEngine engine) {
		axiomsCreated = false;
		return true;
	}

	public void intern() {
		createAxioms();
	}
	public AffineTerm getAffineTerm() {
		return m_affineTerm;
	}
	public void accept(FlatTermVisitor visitor) {
		visitor.visit(this);
	}
}
