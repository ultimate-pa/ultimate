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
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IFreshTermVariableConstructor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SafeSubstitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;

/**
 * Data structure that represents a quantified formula but allows one to
 * explicitly access leading quantifiers and quantified variables.
 * Two blocks with the same quantifier are merged into one block, e.g., 
 * the term ∃x.∃y x=y becomes ∃x,y. x=y
 * Furthermore we remove variables the do not occur freely in the subformula,
 * e.g., the term ∃x,y.∀x. x=y becomes ∃y.∀x. x=y
 * 
 * @author Matthias Heizmann
 * 
 */
public class QuantifierSequence {
	private final Script m_Script;
	private final List<QuantifiedVariables> m_QuantifierBlocks = new ArrayList<>();
	private Term m_InnerTerm;

	public QuantifierSequence(final Script script, 
			final Term input) {
		m_Script = script;
		Term innerTerm = input;
		while(innerTerm instanceof QuantifiedFormula) {
			final QuantifiedFormula qf = (QuantifiedFormula) innerTerm;
			final Set<TermVariable> variables = SmtUtils.filterToVarsThatOccurFreelyInTerm(
					Arrays.asList(qf.getVariables()), qf.getSubformula()); 
			final int quantifier = qf.getQuantifier();
			if (m_QuantifierBlocks.isEmpty() || m_QuantifierBlocks.get(m_QuantifierBlocks.size()-1).getQuantifier() != quantifier) {
				final QuantifiedVariables qv = new QuantifiedVariables(qf.getQuantifier(), variables);
				m_QuantifierBlocks.add(qv);
			} else {
				final QuantifiedVariables last = m_QuantifierBlocks.remove(m_QuantifierBlocks.size()-1);
				final Set<TermVariable> newQuantifiedVariables = new HashSet<>(last.getVariables());
				newQuantifiedVariables.addAll(variables);
				m_QuantifierBlocks.add(new QuantifiedVariables(quantifier, newQuantifiedVariables));
			}
			innerTerm = qf.getSubformula();
		}
		m_InnerTerm = innerTerm;
	}
	
	
	/**
	 * Prepend a sequence of quantifiers to a term.
	 */
	public static Term prependQuantifierSequence(Script script, 
			List<QuantifiedVariables> quantifierSequence, final Term term) {
		Term result = term;
		for (int i = quantifierSequence.size()-1; i>=0; i--) {
			final QuantifiedVariables quantifiedVars = quantifierSequence.get(i);
			result = script.quantifier(quantifiedVars.getQuantifier(), 
					quantifiedVars.getVariables().toArray(
							new TermVariable[quantifiedVars.getVariables().size()]), result);
		}
		return result;
	}
	
	public Term getInnerTerm() {
		return m_InnerTerm;
	}

	public Term toTerm() {
		return prependQuantifierSequence(m_Script, m_QuantifierBlocks, m_InnerTerm);
	}
	
	public void replace(final Set<TermVariable> forbiddenVariables, 
			final IFreshTermVariableConstructor freshVarConstructor,
			final String replacementName) {
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (QuantifiedVariables qv : m_QuantifierBlocks) {
			for (TermVariable tv : forbiddenVariables) {
				if (qv.m_Variables.contains(tv)) {
					final TermVariable fresh = freshVarConstructor.constructFreshTermVariable(
							replacementName, tv.getSort());
					substitutionMapping.put(tv, fresh);
					qv.m_Variables.remove(tv);
					qv.m_Variables.add(fresh);
				}
			}
		}
		m_InnerTerm = (new SafeSubstitution(m_Script, substitutionMapping)).transform(m_InnerTerm);
	}
	
	public static Term mergeQuantifierSequences(final Script script, 
			final IFreshTermVariableConstructor freshVarConstructor, 
			final String functionSymbolName, 
			final QuantifierSequence[] quantifierSequences) {
		// sort sequences, sequence with largest number of blocks first 
		Arrays.sort(quantifierSequences, Collections.reverseOrder(Comparator.comparing(
				QuantifierSequence::getNumberOfQuantifierBlocks)));
		
		final QuantifierSequence largestSequence = quantifierSequences[0];
		final List<QuantifiedVariables> resultQuantifierBlocks = 
				new ArrayList<QuantifiedVariables>(largestSequence.getNumberOfQuantifierBlocks());
		final Term innerTerms[] = new Term[quantifierSequences.length];
		for (int i=0; i<largestSequence.getNumberOfQuantifierBlocks(); i++) {
			final int quantifierOfLargestSequence = 
					largestSequence.getQuantifierBlocks().get(i).getQuantifier();
			resultQuantifierBlocks.add(new QuantifiedVariables(
					quantifierOfLargestSequence, new HashSet<>()));
		}
		assert resultQuantifierBlocks.size() == largestSequence.getNumberOfQuantifierBlocks();
		
		Set<TermVariable> occurredVariables = new HashSet<>();
		for (int i=0; i<quantifierSequences.length; i++) {
			quantifierSequences[i].replace(occurredVariables, freshVarConstructor, "prenex");
			innerTerms[i] = quantifierSequences[i].getInnerTerm();
			if (quantifierSequences[i].getNumberOfQuantifierBlocks() > 0) {
				integrateQuantifierBlocks(resultQuantifierBlocks, quantifierSequences[i].getQuantifierBlocks());
			}
		}
		final Term resultInnerTerm;
		if (functionSymbolName.equals("and")) {
			resultInnerTerm = Util.and(script, innerTerms);
		} else if (functionSymbolName.equals("or")) {
			resultInnerTerm = Util.or(script, innerTerms);
		} else {
			throw new IllegalArgumentException("unsupported " + functionSymbolName);
		}
		final Term result = prependQuantifierSequence(script, 
				resultQuantifierBlocks, resultInnerTerm);
		return result; 
	}
	
	
	
	private static void integrateQuantifierBlocks(List<QuantifiedVariables> resultQuantifierBlocks,
			List<QuantifiedVariables> quantifierBlocks) {
		final int offset;
		{
			final int lastQuantifierResult = resultQuantifierBlocks.get(resultQuantifierBlocks.size()-1).getQuantifier();
			final int lastQuantifierCurrent = quantifierBlocks.get(quantifierBlocks.size()-1).getQuantifier();
			if (lastQuantifierResult == lastQuantifierCurrent) {
				offset = resultQuantifierBlocks.size() - quantifierBlocks.size();
			} else {
				if (resultQuantifierBlocks.size() == quantifierBlocks.size()) {
					// special case where both sequences have same size but
					// start with different quantifiers
					resultQuantifierBlocks.add(new QuantifiedVariables(lastQuantifierCurrent, new HashSet<>()));
				} 
				offset = resultQuantifierBlocks.size() - quantifierBlocks.size();
			}
			assert offset >= 0;
		}
		for (int i=0; i<quantifierBlocks.size(); i++) {
			assert resultQuantifierBlocks.get(i+offset).getQuantifier() == 
					quantifierBlocks.get(i).getQuantifier() : "wrong offset";
			resultQuantifierBlocks.get(i+offset).getVariables().addAll(quantifierBlocks.get(i).getVariables());
		}
	}


	public List<QuantifiedVariables> getQuantifierBlocks() {
		return m_QuantifierBlocks;
	}
	
	public int getNumberOfQuantifierBlocks() {
		return m_QuantifierBlocks.size();
	}
	
	@Override
	public String toString() {
		return m_QuantifierBlocks + " " + m_InnerTerm;
	}


	public static class QuantifiedVariables {
		private final int m_Quantifier;
		private final Set<TermVariable> m_Variables;
		public QuantifiedVariables(int quantifier, Set<TermVariable> variables) {
			super();
			m_Quantifier = quantifier;
			m_Variables = variables;
		}
		public int getQuantifier() {
			return m_Quantifier;
		}
		public Set<TermVariable> getVariables() {
			return m_Variables;
		}
		@Override
		public String toString() {
			return ((m_Quantifier == 0) ? "exists" : "forall") + m_Variables + ". ";
		}
		
		
	}

}
