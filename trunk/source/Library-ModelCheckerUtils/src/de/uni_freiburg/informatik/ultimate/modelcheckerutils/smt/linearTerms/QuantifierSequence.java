/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IFreshTermVariableConstructor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SafeSubstitution;

/**
 * Auxiliary class for the handling of nested quantified formulas.
 * 
 * @author Matthias Heizmann
 * 
 */
public class QuantifierSequence {
	private final Script m_Script;
	private final List<LinkedHashSet<TermVariable>> m_List = new ArrayList<>();
	private final static String s_FreshVariableString = "prenex";

	public QuantifierSequence(Script script) {
		m_Script = script;
		m_List.add(new LinkedHashSet<TermVariable>());
	}

	public Term extractQuantifiers(Term term, boolean replaceVariables, IFreshTermVariableConstructor ftvc) {
		int numberOfAlternations = 0;
		while (term instanceof QuantifiedFormula) {
			assert m_List.size() >= numberOfAlternations + 1;
			QuantifiedFormula quantifiedArg = (QuantifiedFormula) term;
			if (numberOfAlternations % 2 != quantifiedArg.getQuantifier()) {
				numberOfAlternations++;
				if (m_List.size() == numberOfAlternations) {
					m_List.add(new LinkedHashSet<TermVariable>());
				}
			}
			if (replaceVariables) {
				Map<Term, Term> substitutionMapping = new HashMap<>();
				for (TermVariable tv : quantifiedArg.getVariables()) {
					TermVariable fresh = ftvc.constructFreshTermVariable(s_FreshVariableString, tv.getSort());
					substitutionMapping.put(tv, fresh);
					addToPosition(fresh, numberOfAlternations);
				}
				term = new SafeSubstitution(m_Script, ftvc, substitutionMapping).transform(quantifiedArg.getSubformula());
			} else {
				for (TermVariable tv : quantifiedArg.getVariables()) {
					addToPosition(tv, numberOfAlternations);
				}
				term = quantifiedArg.getSubformula();
			}
		}
		return term;
	}

	private void addToPosition(TermVariable tv, int numbersOfAlternation) {
		m_List.get(numbersOfAlternation).add(tv);
	}

	
	public Term prependQuantifierSequence(final Term term) {
		Term result = term;
		for (int i=m_List.size()-1; i>=0; i--) {
			m_List.get(i);
			final int quantor = i % 2;
			final TermVariable[] vars = m_List.get(i).toArray(new TermVariable[m_List.get(i).size()]);
			if (vars.length != 0) {
				result = m_Script.quantifier(quantor, vars, result);
			}
		}
		return result;
	}


}
