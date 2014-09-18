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
package de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.RankVar;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVar;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;


/**
 * Replaces booleans variables b by integer replacement variables rep_b whose
 * semantics is rep_b = (ite b 1 0) 
 * 
 * @author Jan Leike, Matthias Heizmann
 */
public class RewriteBooleans extends TransformerPreProcessor {
	private static final String s_repInPostfix  = "_in_bool";
	private static final String s_repOutPostfix = "_out_bool";
	private static final String s_repVarSortName = "Int"; // FIXME: this should depend on the logic
	
	/**
	 * The sort to be used for new replacement TermVariable's
	 */
	private Sort m_repVarSort;
	
	/**
	 * Maps boolean-valued TermVariable's to their translated counterpart,
	 * which are int- or real-valued variables
	 */
	private final Map<Term, Term> m_SubstitutionMapping;
	
	/**
	 * Factory for construction of auxVars.
	 */
	private final ReplacementVarFactory m_VarFactory;
	
	private final Script m_Script;
	
	
	/**
	 * Create a new RewriteBooleans preprocessor
	 * @param rankVarCollector collecting the new in- and outVars
	 * @param script the Script for creating new variables
	 */
	public RewriteBooleans(ReplacementVarFactory varFactory, Script script) {
		m_VarFactory = varFactory;
		m_Script = script;
		m_repVarSort = m_Script.sort(s_repVarSortName);
		m_SubstitutionMapping = new LinkedHashMap<Term, Term>();
	}
	
	/**
	 * Get the replacement variable corresponding to a (boolean) BoogieVar.
	 * Creates a new replacement variable, if needed.
	 */
	private ReplacementVar getOrConstructReplacementVar(RankVar rankVar) {
		Term definition = getDefinition(
				m_Script, rankVar.getDefinition());
		ReplacementVar repVar = m_VarFactory.
				getOrConstuctReplacementVar(definition);
		return repVar;
	}
	
	/**
	 * Create new integer- or real-valued replacement variables for all boolean
	 * variables.
	 * @param transFormula the transition formula from which the term originated
	 */
	private void generateRepVars(TransFormulaLR tf) {
		Collection<Map.Entry<RankVar, Term>> entrySet =
				new ArrayList<Map.Entry<RankVar, Term>>(
						tf.getInVars().entrySet());
		for (Map.Entry<RankVar, Term> entry : entrySet) {
			if (entry.getValue().getSort().getName().equals("Bool")) {
				ReplacementVar repVar = 
						getOrConstructReplacementVar(entry.getKey());
				Term newInVar = 
						m_SubstitutionMapping.get(entry.getValue());
				if (newInVar == null) {
					// Create a new TermVariable
					newInVar = m_VarFactory.getOrConstructAuxVar(
							repVar.getGloballyUniqueId() + s_repInPostfix,
						m_repVarSort
					);
					m_SubstitutionMapping.put(entry.getValue(), newInVar);
				}
				tf.removeInVar(entry.getKey());
				tf.addInVar(repVar, newInVar);
			}
		}
		entrySet = new ArrayList<Map.Entry<RankVar, Term>>(
						tf.getOutVars().entrySet());
		for (Map.Entry<RankVar, Term> entry : entrySet) {
			if (entry.getValue().getSort().getName().equals("Bool")) {
				ReplacementVar repVar = 
						getOrConstructReplacementVar(entry.getKey());
				Term newOutVar = 
						m_SubstitutionMapping.get(entry.getValue());
				if (newOutVar == null) {
					// Create a new TermVariable
					newOutVar = m_VarFactory.getOrConstructAuxVar(
							repVar.getGloballyUniqueId() + s_repOutPostfix,
						m_repVarSort
					);
					m_SubstitutionMapping.put(entry.getValue(), newOutVar);
				}
				tf.removeOutVar(entry.getKey());
				tf.addOutVar(repVar, newOutVar);
			}
		}
	}
	
	@Override
	public String getDescription() {
		return "Replace boolean variables by integer variables";
	}
	
	@Override
	protected TransFormulaLR process(Script script, TransFormulaLR tf) throws TermException {
		this.generateRepVars(tf);
		return super.process(m_Script, tf);
	}
	
	/**
	 * Given the Term booleanTerm whose Sort is "Bool" return the term
	 * (ite booleanTerm one zero)
	 */
	private Term getDefinition(Script script, Term booleanTerm) {
		assert booleanTerm.getSort().getName().equals("Bool");
		Term one = script.numeral(BigInteger.ONE);
		Term zero = script.numeral(BigInteger.ZERO);
		return script.term("ite", booleanTerm, one, zero);
	}
	
	@Override
	protected TermTransformer getTransformer(Script script) {
		return new RewriteBooleanTransformer(script);
	}
	
	/**
	 * TermTransformer that replaces Boolean TermVariables.  
	 *
	 */
	private class RewriteBooleanTransformer extends TermTransformer {
		private final Script m_Script;
		
		RewriteBooleanTransformer(Script script) {
			assert script != null;
			m_Script = script;
		}
		
		@Override
		protected void convert(Term term) {
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