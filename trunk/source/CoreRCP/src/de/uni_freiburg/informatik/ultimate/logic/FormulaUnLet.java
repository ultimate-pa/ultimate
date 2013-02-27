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

import java.util.Arrays;
import java.util.HashSet;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

/**
 * This class removes all let terms from the formula.  The result 
 * @author Jochen Hoenicke
 */
public class FormulaUnLet extends TermTransformer {
	
	public enum UnletType {
		/**
		 * The SMTLIB compliant unlet that does not expand definitions.
		 */
		SMTLIB(false, false),
		/**
		 * The non-SMTLIB compliant unlet that does not expand definitions but
		 * uses the lazy semantics.
		 */
		LAZY(true, false),
		/**
		 * The SMTLIB compliant unlet that expands definitions.
		 */
		EXPAND_DEFINITIONS(false, true);
		/**
		 * True for lazy let semantics.  The normal semantics of SMTLIB is non-lazy,
		 * i.e. the values of a let are evaluated before they are assigned to 
		 * the corresponding variable.  With lazy let, the value is expanded only
		 * when the variable is used later.  This was useful once for interpolation.
		 */
		final boolean m_IsLazy;
		/**
		 * Should defined functions be expanded.  Defaults to false.
		 */
		final boolean m_ExpandDefinitions;
		UnletType(boolean lazy, boolean expandDefinitions) {
			m_IsLazy = lazy;
			m_ExpandDefinitions = expandDefinitions;
		}
	}
	
	/**
	 * The scoped let map. Each scope corresponds to a partially executed let 
	 * or a quantifier on the todo stack.  It gives the mapping for each 
	 * term variable defined in that scope to the corresponding term.
	 */
	private ScopedHashMap<TermVariable,Term> m_LetMap = new ScopedHashMap<TermVariable, Term>();

	/**
	 * The type of this unletter.
	 */
	private UnletType m_Type;
	
	/**
	 * Create a FormulaUnLet with the standard SMT-LIB semantics for let.
	 */
	public FormulaUnLet() {
		this(UnletType.SMTLIB);
	}
	
	/**
	 * Create a FormulaUnLet.
	 * @param type  The type of the unletter.
	 */
	public FormulaUnLet(UnletType type) {
		m_Type = type;
	}
	
	/**
	 * Add user defined substitutions.  This allows to map variables to
	 * terms, without adding a surrounding let term first.  Note that these
	 * substitutions are then used for all formulas unletted by this class.
	 * @param termSubst The substitution, which maps term variables to
	 * the term with which they should be substituted. 
	 */
	public void addSubstitutions(Map<TermVariable, Term> termSubst) {
		m_LetMap.putAll(termSubst);
	}

	/**
	 * Unlet a term, i.e., remove all LetTerm and replace the term variables
	 * accordingly.
	 * @param term the term to unlet
	 * @return the resulting let-free term.
	 */
	public Term unlet(Term term) {
		return transform(term);
	}

	@Override
	public void convert(Term term) {
		if (term instanceof TermVariable) {
			Term value = m_LetMap.get((TermVariable)term);
			if (value == null) {
				setResult(term);
			} else if (m_Type.m_IsLazy) {
				pushTerm(value);
			} else {
				setResult(value);
			}
		} else if (m_Type.m_IsLazy && term instanceof LetTerm) {
			LetTerm letTerm = (LetTerm) term;
			preConvertLet(letTerm, letTerm.getValues());
		} else if (term instanceof QuantifiedFormula) {
			QuantifiedFormula qf = (QuantifiedFormula)term;
			TermVariable[] vars = qf.getVariables();
			Theory theory = term.getTheory();

			/* check which variables are in the image of the substitution */
			HashSet<TermVariable> used = new HashSet<TermVariable>();
			for (Map.Entry<TermVariable,Term> substTerms : m_LetMap.entrySet()) {
				if (!Arrays.asList(vars).contains(substTerms.getKey()))
					used.addAll(Arrays.asList(substTerms.getValue().getFreeVars()));
			}
			m_LetMap.beginScope();
			for (int i = 0; i < vars.length; i++) {
				if (used.contains(vars[i])) {
					m_LetMap.put(vars[i], theory
						.createFreshTermVariable("unlet", vars[i].getSort()));
				} else {
					if (m_LetMap.containsKey(vars[i]))
						m_LetMap.remove(vars[i]);
				}
			}
			super.convert(term);
		} else if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			if (m_Type.m_ExpandDefinitions &&
					appTerm.getFunction().getDefinition() != null) {
				FunctionSymbol defed = appTerm.getFunction();
				Term fakeLet = appTerm.getTheory().let(
						defed.getDefinitionVars(), appTerm.getParameters(),
						defed.getDefinition());
				pushTerm(fakeLet);
				return;
			}
			super.convert(term);
		} else
			super.convert(term);
	}

	@Override
	public void preConvertLet(LetTerm oldLet, Term[] newValues) {
		m_LetMap.beginScope();
		TermVariable[] vars = oldLet.getVariables();
		for (int i = 0; i < vars.length; i++)
			m_LetMap.put(vars[i], newValues[i]);
		super.preConvertLet(oldLet, newValues);
	}
	
	@Override
	public void postConvertLet(LetTerm oldLet, Term[] newValues, Term newBody) {
		setResult(newBody);
		m_LetMap.endScope();
	}
	
	/**
	 * Collect the sub term of a quantified formula and build the converted 
	 * formula.  The converted sub formula is expected to be on the
	 * converted stack. This also ends the scope of the quantifier.
	 * It stores the converted quantifier on the converted stack and in the
	 * cache.
	 * @param quant the quantifier to convert.
	 */
	@Override
	public void postConvertQuantifier(QuantifiedFormula old, Term newBody) {
		TermVariable[] vars = old.getVariables();
		TermVariable[] newVars = vars;
		for (int i = 0; i < vars.length; i++) {
			Term newVar = m_LetMap.get(vars[i]);
			if (newVar != null) {
				if (vars == newVars)
					newVars = vars.clone();
				newVars[i] = (TermVariable) newVar; 
			}
		}
		m_LetMap.endScope();
		if (vars != newVars || old.getSubformula() != newBody) {
			Theory theory = old.getTheory();
			setResult(old.getQuantifier() == QuantifiedFormula.EXISTS
					? theory.exists(newVars, newBody)
					: theory.forall(newVars, newBody));
		} else {
			setResult(old);
		}
	}
}
