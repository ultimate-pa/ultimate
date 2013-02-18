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
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * This class removes all let terms from the formula.  The result 
 * @author Jochen Hoenicke
 */
public class FormulaSubstitutor extends TermTransformer {
	/**
	 * The substitution map.  It gives the mapping for each 
	 * term variable that should be substituted to its corresponding term.
	 */
	private HashMap<TermVariable,Term> m_SubstMap = new HashMap<TermVariable, Term>();

	/**
	 * Create a FormulaSubstitutor.
	 */
	public FormulaSubstitutor() {
	}
	
	/**
	 * Add user defined substitutions.  This allows to map variables to
	 * terms, without adding a surrounding let term first.  Note that these
	 * substitutions are then used for all formulas unletted by this class.
	 * @param termSubst The substitution, which maps term variables to
	 * the term with which they should be substituted. 
	 */
	public void addSubstitution(TermVariable var, Term subst) {
		m_SubstMap.put(var, subst);
	}
	
	/**
	 * Convert the given term.  It will eventually put the converted term
	 * on the converted stack.  However, since it is recursion free it will
	 * in many cases just reschedule the conversion of the term with a
	 * different task value and add the arguments to the todo stack.
	 * @param term the term to convert.
	 */
	protected void convert(Term term) {
		if (term instanceof TermVariable) {
			TermVariable tv = (TermVariable) term;
			Term newValue = m_SubstMap.get(tv);
			if (newValue != null)
				term = newValue;
		}
		super.convert(term);
	}
}
