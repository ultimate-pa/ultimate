/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.RankVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.ReplacementVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.VarCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.VarFactory;


/**
 * Replaces booleans variables b by integer replacement variables rep_b whose
 * semantics is rep_b = (ite b 1 0) 
 * 
 * @author Jan Leike, Matthias Heizmann
 */
public class RewriteBooleans implements PreProcessor {
	private static final String s_repInPostfix  = "_in_bool";
	private static final String s_repOutPostfix = "_out_bool";
	private static final String s_repVarSortName = "Real";
	
	private Script m_Script;
	
	/**
	 * The sort to be used for new replacement TermVariable's
	 */
	private Sort m_repVarSort;
	
	/**
	 * For generating replacement variables
	 */
	private final VarCollector m_rankVarCollector;
	
	/**
	 * A collection of the generated replacement variables.
	 * Used only for debugging.
	 */
	private final Collection<ReplacementVar> m_repVars;
	
	/**
	 * Maps boolean-valued TermVariable's to their translated counterpart,
	 * which are int- or real-valued variables
	 */
	private final Map<Term, Term> m_SubstitutionMapping;
	
	/**
	 * Create a new RewriteBooleans preprocessor
	 * @param rankVarCollector collecting the new in- and outVars
	 * @param script the Script for creating new variables
	 */
	public RewriteBooleans(VarCollector rankVarCollector) {
		m_rankVarCollector = rankVarCollector;
		m_SubstitutionMapping = new LinkedHashMap<Term, Term>();
		m_repVars = new ArrayList<ReplacementVar>();

		
	}
	
	/**
	 * Get the replacement variable corresponding to a (boolean) BoogieVar.
	 * Creates a new replacement variable, if needed.
	 */
	private ReplacementVar getOrConstructReplacementVar(RankVar rankVar) {
		String rankVarId = rankVar.getGloballyUniqueId();
		VarFactory rvFactory = m_rankVarCollector.getFactory();
		ReplacementVar repVar = rvFactory.getRepVar(rankVarId);
		if (repVar == null) {
			String name = rankVarId + "_bool";
			repVar = new ReplacementVar(name,
					getDefinition(rankVar.getDefinition()));
			rvFactory.registerRepVar(rankVar.getGloballyUniqueId(), repVar);
			m_repVars.add(repVar);
		}
		return repVar;
	}
	
	/**
	 * Create new integer- or real-valued replacement variables for all boolean
	 * variables.
	 * @param transFormula the transition formula from which the term originated
	 */
	private void generateRepVars() {
		VarFactory rvFactory = m_rankVarCollector.getFactory();
		Collection<Map.Entry<RankVar, Term>> entrySet =
				new ArrayList<Map.Entry<RankVar, Term>>(
						m_rankVarCollector.getInVars().entrySet());
		for (Map.Entry<RankVar, Term> entry : entrySet) {
			if (entry.getValue().getSort().getName().equals("Bool")) {
				ReplacementVar repVar = 
						getOrConstructReplacementVar(entry.getKey());
				Term newInVar = 
						m_SubstitutionMapping.get(entry.getValue());
				if (newInVar == null) {
					// Create a new TermVariable
					newInVar = rvFactory.getNewTermVariable(
							repVar.getGloballyUniqueId() + s_repInPostfix,
						m_repVarSort
					);
					m_SubstitutionMapping.put(entry.getValue(), newInVar);
				}
				m_rankVarCollector.removeInVar(entry.getKey());
				m_rankVarCollector.addInVar(repVar, newInVar);
			}
		}
		entrySet = new ArrayList<Map.Entry<RankVar, Term>>(
						m_rankVarCollector.getOutVars().entrySet());
		for (Map.Entry<RankVar, Term> entry : entrySet) {
			if (entry.getValue().getSort().getName().equals("Bool")) {
				ReplacementVar repVar = 
						getOrConstructReplacementVar(entry.getKey());
				Term newOutVar = 
						m_SubstitutionMapping.get(entry.getValue());
				if (newOutVar == null) {
					// Create a new TermVariable
					newOutVar = rvFactory.getNewTermVariable(
							repVar.getGloballyUniqueId() + s_repOutPostfix,
						m_repVarSort
					);
					m_SubstitutionMapping.put(entry.getValue(), newOutVar);
				}
				m_rankVarCollector.removeOutVar(entry.getKey());
				m_rankVarCollector.addOutVar(repVar, newOutVar);
			}
		}
	}
	
	@Override
	public String getDescription() {
		return "Replaces boolean variables by replacement integer variables";
	}
	
	@Override
	public Term process(Script script, Term term) {
		m_Script = script;
		m_repVarSort = m_Script.sort(s_repVarSortName);
		generateRepVars();
		return (new RewriteBooleanHelper()).transform(term);
	}
	
	/**
	 * Given the Term booleanTerm whose Sort is "Bool" return the term
	 * (ite booleanTerm one zero)
	 */
	private Term getDefinition(Term booleanTerm) {
		assert booleanTerm.getSort().getName().equals("Bool");
		Term one = m_Script.numeral(BigInteger.ONE);
		Term zero = m_Script.numeral(BigInteger.ZERO);
		return m_Script.term("ite", booleanTerm, one, zero);
	}
	
	/**
	 * TermTransformer that replaces Boolean TermVariables.  
	 *
	 */
	private class RewriteBooleanHelper extends TermTransformer {
		@Override
		protected void convert(Term term) {
			assert(m_Script != null);
			if (term instanceof TermVariable &&
					term.getSort().getName().equals("Bool")) {
				TermVariable var = (TermVariable) term;
				assert m_SubstitutionMapping.containsKey(var);
				Term translatedVar = m_SubstitutionMapping.get(var);
				Term one = m_Script.numeral(BigInteger.ONE);
				Term repTerm = m_Script.term(">=", translatedVar, one);
				setResult(repTerm);
				return;
			}
			super.convert(term);
		}
	}
}