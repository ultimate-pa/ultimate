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
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

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
	public static final String s_Description = "Replace boolean variables by integer variables";
	
	private static final String s_repInPostfix  = "_in_bool";
	private static final String s_repOutPostfix = "_out_bool";
	private static final String s_repInOutPostfix = "_inout_bool";
	private static final String s_repAuxPostfix = "_aux_bool";
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
	private void generateRepAndAuxVars(TransFormulaLR tf) {
		ArrayList<RankVar> rankVarsWithDistinctInVar = new ArrayList<>();
		ArrayList<RankVar> rankVarsWithDistinctOutVar = new ArrayList<>();
		ArrayList<RankVar> rankVarsWithCommonInVarOutVar = new ArrayList<>();
		for (Map.Entry<RankVar, Term> entry : tf.getInVars().entrySet()) {
			if (isBool(entry.getValue())) {
				if (TransFormulaUtils.inVarAndOutVarCoincide(entry.getKey(), tf)) {
					rankVarsWithCommonInVarOutVar.add(entry.getKey());
				} else {
					rankVarsWithDistinctInVar.add(entry.getKey());
				}
			}
		}
		for (Map.Entry<RankVar, Term> entry : tf.getOutVars().entrySet()) {
			if (isBool(entry.getValue())) {
				if (TransFormulaUtils.inVarAndOutVarCoincide(entry.getKey(), tf)) {
					// do nothing, was already added
				} else {
					rankVarsWithDistinctOutVar.add(entry.getKey());
				}
			}
		}

		for (RankVar rv : rankVarsWithCommonInVarOutVar) {
			ReplacementVar repVar = getOrConstructReplacementVar(rv);
			TermVariable newInOutVar = m_VarFactory.getOrConstructAuxVar(
					repVar.getGloballyUniqueId() + s_repInOutPostfix, m_repVarSort);
			Term replacementTerm = constructReplacementTerm(newInOutVar);
			m_SubstitutionMapping.put(tf.getInVars().get(rv), replacementTerm);
			tf.removeInVar(rv);
			tf.addInVar(repVar, newInOutVar);
			tf.removeOutVar(rv);
			tf.addOutVar(repVar, newInOutVar);
		}

		for (RankVar rv : rankVarsWithDistinctInVar) {
			ReplacementVar repVar = getOrConstructReplacementVar(rv);
			TermVariable newInVar = m_VarFactory.getOrConstructAuxVar(
					repVar.getGloballyUniqueId() + s_repInPostfix, m_repVarSort);
			Term replacementTerm = constructReplacementTerm(newInVar);
			m_SubstitutionMapping.put(tf.getInVars().get(rv), replacementTerm);
			tf.removeInVar(rv);
			tf.addInVar(repVar, newInVar);
		}
		
		for (RankVar rv : rankVarsWithDistinctOutVar) {
			ReplacementVar repVar = getOrConstructReplacementVar(rv);
			TermVariable newOutVar = m_VarFactory.getOrConstructAuxVar(
					repVar.getGloballyUniqueId() + s_repOutPostfix, m_repVarSort);
			Term replacementTerm = constructReplacementTerm(newOutVar);
			m_SubstitutionMapping.put(tf.getOutVars().get(rv), replacementTerm);
			tf.removeOutVar(rv);
			tf.addOutVar(repVar, newOutVar);
		}
		
		Set<TermVariable> auxVars = tf.getAuxVars();
		for (TermVariable tv : auxVars) {
			if (isBool(tv)) {
				TermVariable newAuxVar = m_VarFactory.getOrConstructAuxVar(
						tv.getName() + s_repAuxPostfix,	m_repVarSort);
				tf.removeAuxVar(tv);
				tf.addAuxVars(Collections.singleton(newAuxVar));
			}
		}
	}
	
	
	/**
	 * return true iff sort of term is Bool.
	 */
	private static final boolean isBool(Term term) {
		return term.getSort().getName().equals("Bool");
	}
	
	private Term constructReplacementTerm(TermVariable tv) {
		Term one = m_Script.numeral(BigInteger.ONE);
		Term repTerm = m_Script.term(">=", tv, one);
		return repTerm;
	}

	
	@Override
	public String getDescription() {
		return s_Description;
	}
	
	@Override
	public TransFormulaLR process(Script script, TransFormulaLR tf) throws TermException {
		this.generateRepAndAuxVars(tf);
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
			if (term instanceof TermVariable && isBool(term)) {
				TermVariable var = (TermVariable) term;
				assert m_SubstitutionMapping.containsKey(var);
				Term repTerm = m_SubstitutionMapping.get(var);
				setResult(repTerm);
				return;
			}
			super.convert(term);
		}

	}
}