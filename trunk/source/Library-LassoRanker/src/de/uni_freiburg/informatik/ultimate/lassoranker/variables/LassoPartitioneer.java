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
package de.uni_freiburg.informatik.ultimate.lassoranker.variables;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.LassoPreProcessor;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.DagSizePrinter;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Cnf;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.UnionFind;

/**
 * Split lasso into independent components.
 * 
 * @author Matthias Heizmann
 *
 */
public class LassoPartitioneer extends LassoPreProcessor {
	private final IUltimateServiceProvider m_Services;
	private final Map<TermVariable, TransFormulaLR> m_OriginalTF = new HashMap<TermVariable, TransFormulaLR>();
	private HashRelation<TermVariable, Term> m_TermVariable2StemConjuncts;
	/**
	 * TermVariables of stem that do not occur in any conjunct (only occur as
	 * inVar or outVar in original lasso.
	 */
	private HashSet<Term> m_StemTermVariablesWithoutConjuncts;
	private HashRelation<TermVariable, Term> m_TermVariable2LoopConjuncts;
	/**
	 * TermVariables of loop that do not occur in any conjunct (only occur as
	 * inVar or outVar in original lasso.
	 */
	private HashSet<Term> m_LoopTermVariablesWithoutConjuncts;
	private final UnionFind<TermVariable> m_EquivalentTermVariables = new UnionFind<>();
	private Set<RankVar> m_AllRankVars = new HashSet<RankVar>();
	private Script m_Script;
	private final List<TransFormulaLR> m_NewStem = new ArrayList<>();
	private final List<TransFormulaLR> m_NewLoop = new ArrayList<>();
	private Logger m_Logger;
	
	/**
	 * Do not modify the lasso builder. Set this to true until support for lasso
	 * builder with more than one stem (resp. loop) is implemented.
	 */
	private final boolean m_DryRun = true;
	
	
	
	
	
	public LassoPartitioneer(IUltimateServiceProvider services) {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
	}


	@Override
	public void process(LassoBuilder lasso_builder) throws TermException {
		m_lassoBuilder = lasso_builder;
		m_Script = lasso_builder.getScript();
		partitioneer();
	}


	public void partitioneer() {
		m_TermVariable2StemConjuncts = new HashRelation<>();
		m_TermVariable2LoopConjuncts = new HashRelation<>();
		m_StemTermVariablesWithoutConjuncts = new HashSet<>();
		m_LoopTermVariablesWithoutConjuncts = new HashSet<>();
		extractTermVariables(m_lassoBuilder.getStemComponents(), m_TermVariable2StemConjuncts, m_StemTermVariablesWithoutConjuncts);
		extractTermVariables(m_lassoBuilder.getLoopComponents(), m_TermVariable2LoopConjuncts, m_LoopTermVariablesWithoutConjuncts);
		
		for (RankVar rv : m_AllRankVars) {
			Set<TermVariable> termVariables = new HashSet<TermVariable>();
			for (TransFormulaLR transFormulaLR : m_lassoBuilder.getStemComponents()) {
				TermVariable inVar = (TermVariable) transFormulaLR.getInVars().get(rv);
				if (inVar != null) {
					termVariables.add(inVar);
				}
				TermVariable outVar = (TermVariable) transFormulaLR.getOutVars().get(rv);
				if (outVar != null) {
					termVariables.add(outVar);
				}
				assert (inVar == null) == (outVar == null) : "both or none";
			}
			for (TransFormulaLR transFormulaLR : m_lassoBuilder.getLoopComponents()) {
				TermVariable inVar = (TermVariable) transFormulaLR.getInVars().get(rv);
				if (inVar != null) {
					termVariables.add(inVar);
				}
				TermVariable outVar = (TermVariable) transFormulaLR.getOutVars().get(rv);
				if (outVar != null) {
					termVariables.add(outVar);
				}
				assert (inVar == null) == (outVar == null) : "both or none"; 
			}
			announceEquivalence(termVariables);
		}
		
		for (TermVariable equivalenceClassRepresentative : 
								m_EquivalentTermVariables.getAllRepresentatives()) {
			Set<TermVariable> termVariableEquivalenceClass = 
					m_EquivalentTermVariables.getEquivalenceClassMembers(equivalenceClassRepresentative);
			Set<Term> equivalentStemConjuncts = new HashSet<Term>();
			Set<TermVariable> equivalentStemVariablesWithoutConjunct = new HashSet<TermVariable>();
			Set<Term> equivalentLoopConjuncts = new HashSet<Term>();
			Set<TermVariable> equivalentLoopVariablesWithoutConjunct = new HashSet<TermVariable>();
			for (TermVariable tv : termVariableEquivalenceClass) {
				if (m_TermVariable2StemConjuncts.getDomain().contains(tv)) {
					equivalentStemConjuncts.addAll(m_TermVariable2StemConjuncts.getImage(tv));
				} else if (m_StemTermVariablesWithoutConjuncts.contains(tv)) {
					equivalentStemVariablesWithoutConjunct.add(tv);
				} else if (m_TermVariable2LoopConjuncts.getDomain().contains(tv)) {
					equivalentLoopConjuncts.addAll(m_TermVariable2LoopConjuncts.getImage(tv));
				} else if (m_LoopTermVariablesWithoutConjuncts.contains(tv)) {
					equivalentLoopVariablesWithoutConjunct.add(tv);
				} else {
					throw new AssertionError("unknown variable " + tv);
				}
			}
			if (!equivalentStemConjuncts.isEmpty() || !equivalentStemVariablesWithoutConjunct.isEmpty()) {
				TransFormulaLR stemTransformulaLR = constructTransFormulaLR(equivalentStemConjuncts, equivalentStemVariablesWithoutConjunct);
				m_NewStem.add(stemTransformulaLR);
			}
			if (!equivalentLoopConjuncts.isEmpty() || !equivalentLoopVariablesWithoutConjunct.isEmpty()) {
				TransFormulaLR loopTransformulaLR = constructTransFormulaLR(equivalentLoopConjuncts, equivalentLoopVariablesWithoutConjunct);
				m_NewLoop.add(loopTransformulaLR);
			}
		}
		if (m_NewStem.isEmpty()) {
			m_NewStem.add(new TransFormulaLR(m_Script.term("true")));
		}

		String messageC = "Stem components before: " + m_lassoBuilder.getStemComponents().size()
				+ " Loop components before: " + m_lassoBuilder.getLoopComponents().size()
				+ " Stem components after: " + m_NewStem.size()
				+ " Loop components after: " + m_NewLoop.size();
		m_Logger.info(messageC);
		String messageS = "Stem maxDagSize before: " + computeMaxDagSize(m_lassoBuilder.getStemComponents())
				+ " Loop maxDagSize before: " + computeMaxDagSize(m_lassoBuilder.getLoopComponents())
				+ " Stem maxDagSize after: " + computeMaxDagSize(m_NewStem)
				+ " Loop maxDagSize after: " + computeMaxDagSize(m_NewLoop);
		m_Logger.info(messageS);

		if (!m_DryRun) {
			m_lassoBuilder.setStemComponents(m_NewStem);
			m_lassoBuilder.setLoopComponents(m_NewLoop);
			
		}
	}
	
	private static int computeMaxDagSize(Collection<TransFormulaLR> components) {
		TreeSet<Integer> sizes = new TreeSet<>();
		for (TransFormulaLR tflr : components) {
			int dagSize = (new DAGSize()).size(tflr.getFormula());
			sizes.add(dagSize);
		}
		return sizes.descendingIterator().next();
	}


	private TransFormulaLR constructTransFormulaLR(
			Set<Term> equivalentStemConjuncts, Set<TermVariable> equivalentVariablesWithoutConjunct) {
		TransFormulaLR transformulaLR;
		Term formula = Util.and(m_Script, equivalentStemConjuncts.toArray(new Term[equivalentStemConjuncts.size()]));
		transformulaLR = new TransFormulaLR(formula);
		for (TermVariable tv : formula.getFreeVars()) {
			addInOuAuxVar(transformulaLR, tv);
		}
		for (TermVariable tv : equivalentVariablesWithoutConjunct) {
			addInOuAuxVar(transformulaLR, tv);
		}
		return transformulaLR;
	}


	private void addInOuAuxVar(TransFormulaLR transformulaLR, TermVariable tv) {
		TransFormulaLR original = m_OriginalTF.get(tv);
		RankVar inVarRankVar = original.getInVarsReverseMapping().get(tv);
		RankVar outVarRankVar = original.getOutVarsReverseMapping().get(tv);
		boolean isAuxVar = original.getAuxVars().contains(tv);
		assert (!isAuxVar || (inVarRankVar == null && outVarRankVar == null)) : "auxVar may neither be inVar nor outVar";
		assert (!(inVarRankVar == null && outVarRankVar == null) || isAuxVar) : "neither inVar nor outVar may be auxVar";
		if (inVarRankVar != null) {
			transformulaLR.addInVar(inVarRankVar, tv);
		}
		if (outVarRankVar != null) {
			transformulaLR.addOutVar(outVarRankVar, tv);
		}
		if (isAuxVar) {
			transformulaLR.addAuxVars(Collections.singleton(tv));
		}
	}


	private HashRelation<TermVariable, Term> extractTermVariables(
			Collection<TransFormulaLR> components, 
			HashRelation<TermVariable, Term> termVariable2conjuncts, 
			HashSet<Term> termVariablesWithoutConjuncts) {
		for (TransFormulaLR tf : components) {
			m_AllRankVars.addAll(tf.getInVars().keySet());
			m_AllRankVars.addAll(tf.getOutVars().keySet());
			//FIXME CNF conversion should be done in advance if desired
			Term cnf = (new Cnf(m_Script, m_Services)).transform(tf.getFormula());
			Term[] conjuncts = SmtUtils.getConjuncts(cnf);
			for (Term conjunct : conjuncts) {
				Set<TermVariable> allTermVariablesOfConjunct = new HashSet<>();
				for (TermVariable tv : conjunct.getFreeVars()) {
					TransFormulaLR oldValue = m_OriginalTF.put(tv, tf);
					assert oldValue == null || oldValue == tf : "may not be modified";
					allTermVariablesOfConjunct.add(tv);
					if (m_EquivalentTermVariables.find(tv) == null) {
						m_EquivalentTermVariables.makeEquivalenceClass(tv);
					}
					announceEquivalence(allTermVariablesOfConjunct);
					termVariable2conjuncts.addPair(tv, conjunct);
				}
			}
			for (Entry<RankVar, Term> entry : tf.getInVars().entrySet()) {
				if (!termVariable2conjuncts.getDomain().contains(entry.getValue())) {
					m_EquivalentTermVariables.makeEquivalenceClass((TermVariable) entry.getValue());
					termVariablesWithoutConjuncts.add(entry.getValue());
					TransFormulaLR oldValue = m_OriginalTF.put((TermVariable) entry.getValue(), tf);
					assert oldValue == null || oldValue == tf : "may not be modified";
				}
			}
			for (Entry<RankVar, Term> entry : tf.getOutVars().entrySet()) {
				if (!termVariable2conjuncts.getDomain().contains(entry.getValue())) {
					m_EquivalentTermVariables.makeEquivalenceClass((TermVariable) entry.getValue());
					termVariablesWithoutConjuncts.add(entry.getValue());
					TransFormulaLR oldValue = m_OriginalTF.put((TermVariable) entry.getValue(), tf);
					assert oldValue == null || oldValue == tf : "may not be modified";
				}
			}
		}
		return termVariable2conjuncts;
	}


	private void announceEquivalence(Set<TermVariable> allRankVarsOfConjunct) {
		TermVariable last = null;
		for (TermVariable tv : allRankVarsOfConjunct) {
			if (last != null) {
				m_EquivalentTermVariables.union(tv, last);
			}
			last = tv;
		}
	}


	@Override
	public String getDescription() {
		return this.getClass().getSimpleName();
	}

}
