/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE LassoRanker Library.
 * 
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors;

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
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SafeSubstitutionWithLocalSimplification;

/**
 * Abstract superclass for preprocessors that replace TermVariables.
 * Note that we have already removed constants 0-ary functions, hence we only
 * have to remove TermVariables
 * 
 * @author Matthias Heizmann
 *
 */
public abstract class RewriteTermVariables extends TransitionPreprocessor {

	/**
	 * The sort to be used for new replacement TermVariable's
	 */
	private final Sort m_repVarSort;

	/**
	 * Compute definition (see {@link RankVar#getDefinition()} for RankVar
	 * that will replace oldRankVar.
	 */
	protected abstract Term constructNewDefinitionForRankVar(RankVar oldRankVar);

	/**
	 * Construct the Term that will replace the old TermVariable for which
	 * we already constructed the new TermVariable newTv.
	 */
	protected abstract Term constructReplacementTerm(TermVariable newTv);

	/**
	 * @return true iff term will be replaced by this preprocessor
	 */
	protected abstract boolean hasToBeReplaced(Term term);

	/**
	 * @return name of the Sort that we use for the new variables.
	 * This has to be either "Int" or "Real".
	 */
	protected abstract String getRepVarSortName();

	/**
	 * @return the suffix that the new TermVariables get. 
	 * This is mainly important for debugging purposes that we can see that
	 * this preprocessor indeed constructed the variable.
	 */
	protected abstract String getTermVariableSuffix();



	/**
	 * Maps TermVariable that have to replaced to the term by which they are
	 * replaced.
	 */
	private final Map<Term, Term> m_SubstitutionMapping;
	
	/**
	 * Factory for construction of auxVars.
	 */
	private final ReplacementVarFactory m_VarFactory;
	protected final Script m_Script;

	public RewriteTermVariables(ReplacementVarFactory varFactory, Script script) {
		m_VarFactory = varFactory;
		m_Script = script;
		m_repVarSort = m_Script.sort(getRepVarSortName());
		m_SubstitutionMapping = new LinkedHashMap<Term, Term>();
	}

	/**
	 * Get the new ReplacementVar for a given RankVar.
	 * Constructs a new replacement variable, if needed.
	 */
	private final ReplacementVar getOrConstructReplacementVar(RankVar rankVar) {
		Term definition = constructNewDefinitionForRankVar(rankVar);
		ReplacementVar repVar = m_VarFactory.
				getOrConstuctReplacementVar(definition);
		return repVar;
	}

	/**
	 * Traverse all inVars, outVars and outVars and construct the new
	 * ReplacementVars and replacing Terms (and put them into the substitution
	 * mapping).
	 */
	private final void generateRepAndAuxVars(TransFormulaLR tf) {
		ArrayList<RankVar> rankVarsWithDistinctInVar = new ArrayList<>();
		ArrayList<RankVar> rankVarsWithDistinctOutVar = new ArrayList<>();
		ArrayList<RankVar> rankVarsWithCommonInVarOutVar = new ArrayList<>();
		for (Map.Entry<RankVar, Term> entry : tf.getInVars().entrySet()) {
			if (hasToBeReplaced(entry.getValue())) {
				if (TransFormulaUtils.inVarAndOutVarCoincide(entry.getKey(), tf)) {
					rankVarsWithCommonInVarOutVar.add(entry.getKey());
				} else {
					rankVarsWithDistinctInVar.add(entry.getKey());
				}
			}
		}
		for (Map.Entry<RankVar, Term> entry : tf.getOutVars().entrySet()) {
			if (hasToBeReplaced(entry.getValue())) {
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
					computeTermVariableName(repVar.getGloballyUniqueId(), true, true), 
					m_repVarSort);
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
					computeTermVariableName(repVar.getGloballyUniqueId(), true, false), 
					m_repVarSort);
			Term replacementTerm = constructReplacementTerm(newInVar);
			m_SubstitutionMapping.put(tf.getInVars().get(rv), replacementTerm);
			tf.removeInVar(rv);
			tf.addInVar(repVar, newInVar);
		}
		
		for (RankVar rv : rankVarsWithDistinctOutVar) {
			ReplacementVar repVar = getOrConstructReplacementVar(rv);
			TermVariable newOutVar = m_VarFactory.getOrConstructAuxVar(
					computeTermVariableName(repVar.getGloballyUniqueId(), false, true), 
					m_repVarSort);
			Term replacementTerm = constructReplacementTerm(newOutVar);
			m_SubstitutionMapping.put(tf.getOutVars().get(rv), replacementTerm);
			tf.removeOutVar(rv);
			tf.addOutVar(repVar, newOutVar);
		}
		
		Set<TermVariable> auxVars = tf.getAuxVars();
		for (TermVariable tv : auxVars) {
			if (hasToBeReplaced(tv)) {
				TermVariable newAuxVar = m_VarFactory.getOrConstructAuxVar(
						computeTermVariableName(tv.getName(), false, false),
						m_repVarSort);
				tf.removeAuxVar(tv);
				tf.addAuxVars(Collections.singleton(newAuxVar));
			}
		}
	}
	
	private final String computeTermVariableName(String baseName, boolean isInVar, boolean isOutVar) {
		final String result;
		if (isInVar) {
			if (isOutVar) {
				result = baseName + "_inout_" + getTermVariableSuffix();
			} else {
				result = baseName + "_in_" + getTermVariableSuffix();
			}
		} else {
			if (isOutVar) {
				result = baseName + "_out_" + getTermVariableSuffix();
			} else {
				result = baseName + "_aux_" + getTermVariableSuffix();
			}
		}
		return result;
	}

	@Override
	public final TransFormulaLR process(Script script, TransFormulaLR tf) throws TermException {
		this.generateRepAndAuxVars(tf);
		TransFormulaLR newTf = new TransFormulaLR(tf);
		Term newFormula = (new SafeSubstitutionWithLocalSimplification(
				m_Script, m_SubstitutionMapping)).transform(tf.getFormula());
		newTf.setFormula(newFormula);
		return newTf;
	}

}
