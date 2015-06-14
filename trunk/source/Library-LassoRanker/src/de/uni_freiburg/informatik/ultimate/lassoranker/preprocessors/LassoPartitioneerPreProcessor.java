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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoBuilder;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoPartitioneer;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IFreshTermVariableConstructor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.NonTheorySymbol;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Cnf;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap2;

/**
 * Split lasso into independent components.
 * 
 * @author Matthias Heizmann
 *
 */
public class LassoPartitioneerPreProcessor extends LassoPreProcessor {
	public static final String s_Description = "LassoPartitioneer";
	
	private final IUltimateServiceProvider m_Services;
	private final IFreshTermVariableConstructor m_FreshTermVariableConstructor;
	
	private Script m_Script;
	private final List<TransFormulaLR> m_NewStemTermination = new ArrayList<>();
	private final List<TransFormulaLR> m_NewLoopTermination = new ArrayList<>();
	private final List<TransFormulaLR> m_NewStemNontermination = new ArrayList<>();
	private final List<TransFormulaLR> m_NewLoopNontermination = new ArrayList<>();

	private Logger m_Logger;
	
	/**
	 * Do not modify the lasso builder?
	 */
	private final boolean m_DryRun = false;
	
	
	
	
	
	public LassoPartitioneerPreProcessor(IUltimateServiceProvider services, 
			IFreshTermVariableConstructor freshTermVariableConstructor) {
		m_Services = services;
		m_FreshTermVariableConstructor = freshTermVariableConstructor;
		m_Logger = m_Services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
	}


	@Override
	public void process(LassoBuilder lasso_builder) throws TermException {
		m_lassoBuilder = lasso_builder;
		m_Script = lasso_builder.getScript();
		
		List<TransFormulaLR> stem_components =
				m_lassoBuilder.getStemComponentsTermination();
		List<TransFormulaLR> loop_components =
				m_lassoBuilder.getLoopComponentsTermination();
		partition(m_lassoBuilder.getStemComponentsTermination(), m_lassoBuilder.getLoopComponentsTermination(), m_NewStemTermination, m_NewLoopTermination);
		partition(m_lassoBuilder.getStemComponentsNonTermination(), m_lassoBuilder.getLoopComponentsNonTermination(), m_NewStemNontermination, m_NewLoopNontermination);
		
		assert !m_NewStemTermination.isEmpty() : "empty stem";
		assert !m_NewLoopTermination.isEmpty() : "empty loop";
		assert m_NewStemTermination.size() == m_NewLoopTermination.size() : "inconsistent component size";
		
		assert !m_NewStemNontermination.isEmpty() : "empty stem";
		assert !m_NewLoopNontermination.isEmpty() : "empty loop";
		assert m_NewStemNontermination.size() == m_NewLoopNontermination.size() : "inconsistent component size";

		String messageC = "Components before/after: " 
				+ loop_components.size() + "/" + m_NewLoopNontermination.size();
		m_Logger.info(messageC);
		String messageS = "Stem maxDagSize before/after: " 
				+ LassoBuilder.computeMaxDagSize(stem_components) + "/" + LassoBuilder.computeMaxDagSize(m_NewStemNontermination)
				+ " Loop maxDagSize before/after: " 
				+ LassoBuilder.computeMaxDagSize(loop_components) + "/" + LassoBuilder.computeMaxDagSize(m_NewLoopNontermination);
		m_Logger.info(messageS);

		if (!m_DryRun) {
			m_lassoBuilder.setStemComponentsTermination(m_NewStemTermination);
			m_lassoBuilder.setStemComponentsNonTermination(m_NewStemNontermination);
			m_lassoBuilder.setLoopComponentsTermination(m_NewLoopTermination);
			m_lassoBuilder.setLoopComponentsNonTermination(m_NewLoopNontermination);
		}
	}


	private void partition(List<TransFormulaLR> stemComponents,
			List<TransFormulaLR> loopComponents,
			List<TransFormulaLR> newStem,
			List<TransFormulaLR> newLoop) {
		assert(stemComponents.size() == loopComponents.size());
		for (int i=0; i<stemComponents.size(); i++) {
			LassoPartitioneer lp = new LassoPartitioneer(m_Services, m_FreshTermVariableConstructor, m_Script, stemComponents.get(i), loopComponents.get(i));
			newStem.addAll(lp.getNewStem());
			newLoop.addAll(lp.getNewLoop());
		}
	}


	@Override
	public String getDescription() {
		return s_Description;
	}
	
	public int maxDagSizeNewStem() {
		return LassoBuilder.computeMaxDagSize(m_NewStemNontermination);
	}
	
	public int maxDagSizeNewLoop() {
		return LassoBuilder.computeMaxDagSize(m_NewLoopNontermination);
	}


}
