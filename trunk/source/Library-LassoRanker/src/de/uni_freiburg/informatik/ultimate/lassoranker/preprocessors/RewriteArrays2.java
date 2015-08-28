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

import java.util.Collection;
import java.util.Collections;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.Activator;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays.ArrayCellRepVarConstructor;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays.IndexSupportingInvariantAnalysis;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays.TransFormulaLRWithArrayCells;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays.TransFormulaLRWithArrayInformation;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoUnderConstruction;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IFreshTermVariableConstructor;

/**
 * Replace term with arrays by term without arrays by introducing replacement
 * variables for all "important" array values and equalities that state the
 * constraints between array indices and array values (resp. their replacement
 * variables).
 * 
 * 
 * @author Matthias Heizmann
 */
public class RewriteArrays2 extends LassoPreprocessor {

	private final Logger mLogger;
	private final IUltimateServiceProvider mServices;
	
	public static final boolean s_AdditionalChecksIfAssertionsEnabled = !false;
	
	public static final String s_Description = 
			"Removes arrays by introducing new variables for each relevant array cell";

	static final String s_AuxArray = "auxArray";

	/**
	 * The script used to transform the formula
	 */
	private final Script m_Script;


//	private final boolean m_SearchAdditionalSupportingInvariants;
	private final TransFormula m_OriginalStem;
	private final TransFormula m_OriginalLoop;
	private final Set<Term> m_ArrayIndexSupportingInvariants;
	private final Set<BoogieVar> m_ModifiableGlobalsAtHonda;
	
	private final ReplacementVarFactory m_ReplacementVarFactory;
	private final IFreshTermVariableConstructor m_FreshTermVariableConstructor;
	private final Boogie2SMT m_boogie2smt;


	private final boolean m_OverapproximateByOmmitingDisjointIndices;

	public RewriteArrays2(boolean overapproximateByOmmitingDisjointIndices,
			TransFormula originalStem, TransFormula originalLoop, Set<BoogieVar> modifiableGlobalsAtHonda,
			IUltimateServiceProvider services, Set<Term> arrayIndexSupportingInvariants, Boogie2SMT boogie2smt, ReplacementVarFactory ReplacementVarFactory) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		m_OriginalStem = originalStem;
		m_OriginalLoop = originalLoop;
		m_ModifiableGlobalsAtHonda = modifiableGlobalsAtHonda;
		m_ArrayIndexSupportingInvariants = arrayIndexSupportingInvariants;
		m_OverapproximateByOmmitingDisjointIndices = overapproximateByOmmitingDisjointIndices;
		m_boogie2smt = boogie2smt;
		m_Script = boogie2smt.getScript();
		m_ReplacementVarFactory = ReplacementVarFactory;
		m_FreshTermVariableConstructor = m_boogie2smt.getVariableManager();
	}
	

	@Override
	public String getName() {
		return getClass().getSimpleName();
	}

	@Override
	public String getDescription() {
		return s_Description;
	}

//	@Override
//	public void process(LassoBuilder lasso_builder) 
//			throws TermException {
//		m_lassoBuilder = lasso_builder;
//		m_Script = lasso_builder.getScript();
//		ReplacementVarFactory replacementVarFactory = lasso_builder.getReplacementVarFactory();
//		
//		Collection<TransFormulaLR> old_stem_components = lasso_builder.getStemComponentsTermination();
////		assert old_stem_components == lasso_builder.getStemComponentsNonTermination();
//		Collection<TransFormulaLR> old_loop_components = lasso_builder.getLoopComponentsTermination();
////		assert old_loop_components == lasso_builder.getLoopComponentsNonTermination();
//		List<TransFormulaLRWithArrayInformation> stemComponents1 = new ArrayList<TransFormulaLRWithArrayInformation>();
//		for (TransFormulaLR stemComponent : old_stem_components) {
//			TransFormulaLRWithArrayInformation test = new TransFormulaLRWithArrayInformation(
//					mServices, stemComponent, replacementVarFactory, m_Script, m_lassoBuilder.getBoogie2SMT().getVariableManager(), null);
//			stemComponents1.add(test);
//		}
//		List<TransFormulaLRWithArrayInformation> loopComponents1 = new ArrayList<TransFormulaLRWithArrayInformation>();
//		for (TransFormulaLR loopComponent : old_loop_components) {
//			TransFormulaLRWithArrayInformation test = new TransFormulaLRWithArrayInformation(
//					mServices, loopComponent, replacementVarFactory, m_Script, m_lassoBuilder.getBoogie2SMT().getVariableManager(), stemComponents1);
//			loopComponents1.add(test);
//		}
//		ArrayCellRepVarConstructor acrvc = new ArrayCellRepVarConstructor(replacementVarFactory, m_Script, stemComponents1, loopComponents1);
//		IndexSupportingInvariantAnalysis isia = new IndexSupportingInvariantAnalysis(acrvc, true, lasso_builder.getBoogie2SMT(), m_OriginalStem, m_OriginalLoop, m_ModifiableGlobalsAtHonda);
//		m_ArrayIndexSupportingInvariants.addAll(isia.getAdditionalConjunctsEqualities());
//		m_ArrayIndexSupportingInvariants.addAll(isia.getAdditionalConjunctsNotEquals());
//		
//		// for termination, we overapproximate by ommiting disjoint indices
//		{
//			List<TransFormulaLRWithArrayCells> stemComponents2 = new ArrayList<TransFormulaLRWithArrayCells>();
//			List<TransFormulaLR> new_stem_components = new ArrayList<TransFormulaLR>(old_stem_components.size());
//			for (TransFormulaLRWithArrayInformation stemComponent : stemComponents1) {
//				TransFormulaLRWithArrayCells test = new TransFormulaLRWithArrayCells(mServices, replacementVarFactory, m_Script, stemComponent, isia, lasso_builder.getBoogie2SMT(), null, true, true);
//				stemComponents2.add(test);
//				new_stem_components.add(test.getResult());
//			}
//			lasso_builder.setStemComponentsTermination(new_stem_components);
//		}
//		
//		// for nontermination, we do not overapproximate
//		{
//			List<TransFormulaLRWithArrayCells> stemComponents2 = new ArrayList<TransFormulaLRWithArrayCells>();
//			List<TransFormulaLR> new_stem_components = new ArrayList<TransFormulaLR>(old_stem_components.size());
//			for (TransFormulaLRWithArrayInformation stemComponent : stemComponents1) {
//				TransFormulaLRWithArrayCells test = new TransFormulaLRWithArrayCells(mServices, replacementVarFactory, m_Script, stemComponent, isia, lasso_builder.getBoogie2SMT(), null, false, true);
//				stemComponents2.add(test);
//				new_stem_components.add(test.getResult());
//			}
//			lasso_builder.setStemComponentsNonTermination(new_stem_components);
//		}
//		
//		// for termination, we overapproximate by ommiting disjoint indices
//		{
//			List<TransFormulaLRWithArrayCells> loopComponents2 = new ArrayList<TransFormulaLRWithArrayCells>();
//			List<TransFormulaLR> new_loop_components = new ArrayList<TransFormulaLR>(old_loop_components.size());
//			for (TransFormulaLRWithArrayInformation loopComponent : loopComponents1) {
//				TransFormulaLRWithArrayCells test = new TransFormulaLRWithArrayCells(mServices, replacementVarFactory, m_Script, loopComponent, isia, lasso_builder.getBoogie2SMT(), acrvc, true, false);
//				loopComponents2.add(test);
//				new_loop_components.add(test.getResult());
//			}
//
//			lasso_builder.setLoopComponentsTermination(new_loop_components);
//		}
//		
//		// for nontermination, we do not overapproximate
//		{
//			List<TransFormulaLRWithArrayCells> loopComponents2 = new ArrayList<TransFormulaLRWithArrayCells>();
//			List<TransFormulaLR> new_loop_components = new ArrayList<TransFormulaLR>(old_loop_components.size());
//			for (TransFormulaLRWithArrayInformation loopComponent : loopComponents1) {
//				TransFormulaLRWithArrayCells test = new TransFormulaLRWithArrayCells(mServices, replacementVarFactory, m_Script, loopComponent, isia, lasso_builder.getBoogie2SMT(), acrvc, false, false);
//				loopComponents2.add(test);
//				new_loop_components.add(test.getResult());
//			}
//
//			lasso_builder.setLoopComponentsNonTermination(new_loop_components);
//		}
//		
//		
//	}

	@Override
	public Collection<LassoUnderConstruction> process(LassoUnderConstruction lasso) throws TermException {
		boolean overapproximate = true;
		TransFormulaLRWithArrayInformation stemTfwai = new TransFormulaLRWithArrayInformation(
					mServices, lasso.getStem(), m_ReplacementVarFactory, m_Script, m_boogie2smt, null);
		TransFormulaLRWithArrayInformation loopTfwai = new TransFormulaLRWithArrayInformation(
					mServices, lasso.getLoop(), m_ReplacementVarFactory, m_Script, m_boogie2smt, stemTfwai);
		ArrayCellRepVarConstructor acrvc = new ArrayCellRepVarConstructor(m_ReplacementVarFactory, m_Script, stemTfwai, loopTfwai);
		IndexSupportingInvariantAnalysis isia = new IndexSupportingInvariantAnalysis(acrvc, true, m_boogie2smt, m_OriginalStem, m_OriginalLoop, m_ModifiableGlobalsAtHonda);
		m_ArrayIndexSupportingInvariants.addAll(isia.getAdditionalConjunctsEqualities());
		m_ArrayIndexSupportingInvariants.addAll(isia.getAdditionalConjunctsNotEquals());
		TransFormulaLRWithArrayCells stem = new TransFormulaLRWithArrayCells(mServices, m_ReplacementVarFactory, m_Script, stemTfwai, isia, m_boogie2smt, null, overapproximate, true);
		TransFormulaLRWithArrayCells loop = new TransFormulaLRWithArrayCells(mServices, m_ReplacementVarFactory, m_Script, loopTfwai, isia, m_boogie2smt, acrvc, overapproximate, false);
		LassoUnderConstruction newLasso = new LassoUnderConstruction(stem.getResult(), loop.getResult());
		assert !s_AdditionalChecksIfAssertionsEnabled || checkStemImplication(
				mServices, mLogger, lasso, newLasso, m_boogie2smt) : "result of RewriteArrays too strong";
		return Collections.singleton(newLasso);
	}
	
	
	private boolean checkStemImplication(IUltimateServiceProvider services, 
			Logger logger,
			LassoUnderConstruction oldLasso,
			LassoUnderConstruction newLasso,
			Boogie2SMT boogie2smt) {
		LBool implies = TransFormulaUtils.implies(mServices, mLogger, 
				oldLasso.getStem(), newLasso.getStem(), m_Script, boogie2smt.getBoogie2SmtSymbolTable());
		if (implies != LBool.SAT && implies != LBool.UNSAT) {
			logger.warn("result of RewriteArrays check is " + implies);
		}
		assert (implies != LBool.SAT) : "result of RewriteArrays too strong";
		return (implies != LBool.SAT);
	}



}