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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar;

import java.math.BigInteger;
import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;


public class LAEquality extends DPLLAtom {
	private LinVar m_Var;
	private Rational m_Bound;
	private ArrayList<CCEquality> m_dependentEqualities;
	int m_StackDepth;
	
	public LAEquality(int stackLevel, LinVar var, Rational bound) {
		super(HashUtils.hashJenkins(~var.hashCode(), bound), stackLevel);
		m_Var = var;
		m_Bound = bound;
		m_dependentEqualities = new ArrayList<CCEquality>();
	}

	public Rational getBound() {
		return m_Bound;
	}

	public LinVar getVar() {
		return m_Var;
	}
	
	@Override
	public String toStringNegated() {
		return "["+hashCode()+"]"+m_Var + " != " + m_Bound;
	}

	public String toString() {
		return "["+hashCode()+"]"+m_Var + " == " + m_Bound;
	}
	
	@Override
	public Term getSMTFormula(Theory smtTheory, boolean quoted) {
		MutableAffinTerm at = new MutableAffinTerm();
		at.add(Rational.ONE, m_Var);
		at.add(m_Bound.negate());
		Sort s = smtTheory.getSort(m_Var.misint ? "Int" : "Real");
		Sort[] binfunc = {s,s};
		FunctionSymbol comp =  
				smtTheory.getFunction("=", binfunc);
		Term res = smtTheory.term(comp,
				at.toSMTLib(smtTheory, m_Var.misint, quoted),
				m_Var.misint ? smtTheory.numeral(BigInteger.ZERO) :
					smtTheory.rational(BigInteger.ZERO,BigInteger.ONE));
		return res;
	}

	public void addDependentAtom(CCEquality eq) {
		m_dependentEqualities.add(eq);
	}
	
	public void removeDependentAtom(CCEquality eq) {
		m_dependentEqualities.remove(eq);
	}
	
	public Iterable<CCEquality> getDependentEqualities() {
		return m_dependentEqualities;
	}
	
	public boolean equals(Object other) {
		if (other instanceof LAEquality) {
			LAEquality o = (LAEquality) other;
			return o.m_Var == m_Var && o.m_Bound.equals(m_Bound);
		}
		return false;
	}
}
