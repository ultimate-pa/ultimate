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
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.Activator;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays.ArrayCellRepVarConstructor;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays.IndexSupportingInvariantAnalysis;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays.TransFormulaLRWithArrayCells;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays.TransFormulaLRWithArrayInformation;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoBuilder;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;

/**
 * Replace term with arrays by term without arrays by introducing replacement
 * variables for all "important" array values and equalities that state the
 * constraints between array indices and array values (resp. their replacement
 * variables).
 * 
 * 
 * @author Matthias Heizmann
 */
public class RewriteArrays2 extends LassoPreProcessor {

	private final Logger mLogger;
	private final IUltimateServiceProvider mServices;

	static final String s_AuxArray = "auxArray";

	/**
	 * The script used to transform the formula
	 */
	private Script m_Script;


//	private final boolean m_SearchAdditionalSupportingInvariants;
	private final TransFormula m_OriginalStem;
	private final TransFormula m_OriginalLoop;
	private final Set<Term> m_ArrayIndexSupportingInvariants;


	private final boolean m_OverapproximateByOmmitingDisjointIndices;
	private TransFormulaLRWithArrayInformation tflrwai;

	public RewriteArrays2(boolean overapproximateByOmmitingDisjointIndices,
			TransFormula originalStem, TransFormula originalLoop,
			IUltimateServiceProvider services, Set<Term> arrayIndexSupportingInvariants) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		m_OriginalStem = originalStem;
		m_OriginalLoop = originalLoop;
		m_ArrayIndexSupportingInvariants = arrayIndexSupportingInvariants;
		m_OverapproximateByOmmitingDisjointIndices = overapproximateByOmmitingDisjointIndices;
		if (overapproximateByOmmitingDisjointIndices) {
			throw new AssertionError("overapproximateByOmmitingDisjointIndices currently not supported");
		}
	}

	@Override
	public String getDescription() {
		return "Removes arrays by introducing new variables for each "
				+ "relevant array cell";
	}

	@Override
	public void process(LassoBuilder lasso_builder) 
			throws TermException {
		m_lassoBuilder = lasso_builder;
		m_Script = lasso_builder.getScript();
		ReplacementVarFactory replacementVarFactory = lasso_builder.getReplacementVarFactory();
		
		Collection<TransFormulaLR> old_stem_components = lasso_builder.getStemComponents();
		Collection<TransFormulaLR> old_loop_components = lasso_builder.getLoopComponents();
		List<TransFormulaLRWithArrayInformation> stemComponents1 = new ArrayList<TransFormulaLRWithArrayInformation>();
		for (TransFormulaLR stemComponent : old_stem_components) {
			TransFormulaLRWithArrayInformation test = new TransFormulaLRWithArrayInformation(mServices, stemComponent, replacementVarFactory, m_Script);
			stemComponents1.add(test);
		}
		List<TransFormulaLRWithArrayInformation> loopComponents1 = new ArrayList<TransFormulaLRWithArrayInformation>();
		for (TransFormulaLR loopComponent : old_loop_components) {
			TransFormulaLRWithArrayInformation test = new TransFormulaLRWithArrayInformation(mServices, loopComponent, replacementVarFactory, m_Script);
			loopComponents1.add(test);
		}
		ArrayCellRepVarConstructor acrvc = new ArrayCellRepVarConstructor(replacementVarFactory, m_Script, stemComponents1, loopComponents1);
		IndexSupportingInvariantAnalysis isia = new IndexSupportingInvariantAnalysis(acrvc, true, lasso_builder.getBoogie2SMT(), m_OriginalStem, m_OriginalLoop);
		m_ArrayIndexSupportingInvariants.addAll(isia.getAdditionalConjunctsEqualities());
		m_ArrayIndexSupportingInvariants.addAll(isia.getAdditionalConjunctsNotEquals());
		
		List<TransFormulaLRWithArrayCells> stemComponents2 = new ArrayList<TransFormulaLRWithArrayCells>();
		Collection<TransFormulaLR> new_stem_components = new ArrayList<TransFormulaLR>(old_stem_components.size());
		for (TransFormulaLRWithArrayInformation stemComponent : stemComponents1) {
			TransFormulaLRWithArrayCells test = new TransFormulaLRWithArrayCells(mServices, replacementVarFactory, m_Script, stemComponent, isia, lasso_builder.getBoogie2SMT(), null);
			stemComponents2.add(test);
			new_stem_components.add(test.getResult());
		}
		
		List<TransFormulaLRWithArrayCells> loopComponents2 = new ArrayList<TransFormulaLRWithArrayCells>();
		Collection<TransFormulaLR> new_loop_components = new ArrayList<TransFormulaLR>(old_loop_components.size());
		for (TransFormulaLRWithArrayInformation loopComponent : loopComponents1) {
			TransFormulaLRWithArrayCells test = new TransFormulaLRWithArrayCells(mServices, replacementVarFactory, m_Script, loopComponent, isia, lasso_builder.getBoogie2SMT(), acrvc);
			loopComponents2.add(test);
			new_loop_components.add(test.getResult());
		}
		lasso_builder.setStemComponents(new_stem_components);
		lasso_builder.setLoopComponents(new_loop_components);
		
	}


}