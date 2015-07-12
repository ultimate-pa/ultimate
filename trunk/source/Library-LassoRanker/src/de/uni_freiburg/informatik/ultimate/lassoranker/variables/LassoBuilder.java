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
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.lassoranker.Lasso;
import de.uni_freiburg.informatik.ultimate.lassoranker.LassoAnalysis.PreprocessingBenchmark;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearTransition;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.LassoPreProcessor;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;


/**
 * 
 * The LassoBuilder class holds the lasso components during preprocessing.
 * With the LassoBuilder we are building two lassos at the same time:
 * an overapproximated lasso (for termination analysis) and
 * an underapproximated lasso (fer nontermination analysis).`
 * 
 * This object is *not* immutable.
 * 
 * @author Jan Leike
 */
public class LassoBuilder {
	/**
	 * The Boogie2SMT object
	 */
	private final Boogie2SMT m_boogie2smt;
	
	/**
	 * Collection of all generated replacement TermVariables
	 */
	private final Collection<TermVariable> m_termVariables;

	/**
	 * Independent lassos
	 * (possibly an overapproximation)
	 */
	private List<LassoUnderConstruction> m_Lassos_t;
	
	/**
	 * Independent lassos
	 * (possibly an underapproximation)
	 */
	private List<LassoUnderConstruction> m_Lassos_nt;

	
	/**
	 * The script used to create terms in the transition formulas
	 */
	private final Script m_Script;
	
	/**
	 * Object that has to be used for getting and constructing ReplacementVars
	 * that occur in this LassoBuilder.
	 */
	private final ReplacementVarFactory m_ReplacementVarFactory;

	private PreprocessingBenchmark m_PreprocessingBenchmark;

	private final Logger m_Logger;
	
	/**
	 * Create a new LassoBuilder object from components
	 * 
	 * @param script the script that created the transition formulae
	 * @param boogie2smt the boogie smt translator
	 * @param stem the stem transition
	 * @param loop the loop transition
	 */
	public LassoBuilder(Logger logger, Script script, Boogie2SMT boogie2smt, TransFormula stem,
			TransFormula loop) {
		assert script != null;
		assert boogie2smt != null;
		m_Logger = logger;
		m_Script = script;
		m_boogie2smt = boogie2smt;
		m_termVariables = new ArrayList<TermVariable>();
		
		m_ReplacementVarFactory =
				new ReplacementVarFactory(m_boogie2smt.getVariableManager());
		
		m_Lassos_t = new ArrayList<>();
		m_Lassos_t.add(new LassoUnderConstruction(
				TransFormulaLR.buildTransFormula(stem, m_ReplacementVarFactory),
				TransFormulaLR.buildTransFormula(loop, m_ReplacementVarFactory)
			));
		m_Lassos_nt = new ArrayList<>();
		m_Lassos_nt.add(new LassoUnderConstruction(
				TransFormulaLR.buildTransFormula(stem, m_ReplacementVarFactory),
				TransFormulaLR.buildTransFormula(loop, m_ReplacementVarFactory)
			));
		
	}
	
	/**
	 * @return the script used to generate the transition formulas
	 */
	public Script getScript() {
		return m_Script;
	}
	
	/**
	 * @return the associated Boogie2SMT object
	 */
	public Boogie2SMT getBoogie2SMT() {
		return m_boogie2smt;
	}
	
	public ReplacementVarFactory getReplacementVarFactory() {
		return m_ReplacementVarFactory;
	}

	/**
	 * @return a collection of all new TermVariable's created with this object
	 */
	public Collection<TermVariable> getGeneratedTermVariables() {
		return Collections.unmodifiableCollection(m_termVariables);
	}
	
//	/**
//	 * Is the stem the same for termination analysis and nontermination analysis?
//	 * @return whether getStemComponentsTermination() == getStemComponentsNonTermination()
//	 */
//	public boolean isStemApproximated() {
//		return m_stem_components_t != m_stem_components_nt;
//	}
//	
//	/**
//	 * Is the loop the same for termination analysis and nontermination analysis?
//	 * @return whether getLoopComponentsTermination() == getLoopComponentsNonTermination()
//	 */
//	public boolean isLoopApproximated() {
//		return m_loop_components_t != m_loop_components_nt;
//	}
	
	/**
	 * @return the lassos (possibly overapproximation)
	 */
	public List<LassoUnderConstruction> getLassosUCTermination() {
		return m_Lassos_t;
	}
	
	/**
	 * @return the lassos (possibly overapproximation)
	 */
	public List<LassoUnderConstruction> getLassosUCNontermination() {
		return m_Lassos_nt;
	}
	
	public void applyPreprocessor(LassoPreProcessor preprocessor) throws TermException {
		ArrayList<LassoUnderConstruction> newLassos_t = new ArrayList<LassoUnderConstruction>();
		for (LassoUnderConstruction lasso : m_Lassos_t) {
			try {
				newLassos_t.addAll(preprocessor.process(lasso));
			} catch (ToolchainCanceledException tce) {
				String taskMessage = "applying " + preprocessor.getName() + " to lasso for termination ";
				if (tce.getRunningTaskInfo() != null) {
					taskMessage += tce.getRunningTaskInfo();
				}
				throw new ToolchainCanceledException(getClass(), taskMessage);
			}
		}
		m_Lassos_t = newLassos_t;
		ArrayList<LassoUnderConstruction> newLassos_nt = new ArrayList<LassoUnderConstruction>();
		for (LassoUnderConstruction lasso : m_Lassos_nt) {
			try {
				newLassos_nt.addAll(preprocessor.process(lasso));
			} catch (ToolchainCanceledException tce) {
				String taskMessage = "applying " + preprocessor.getName() + " to lasso for nontermination ";
				if (tce.getRunningTaskInfo() != null) {
					taskMessage += tce.getRunningTaskInfo();
				}
				throw new ToolchainCanceledException(getClass(), taskMessage);
			}
		}
		m_Lassos_nt = newLassos_nt;
	}
	
	
	/**
	 * Run a few sanity checks
	 * @return false if something is fishy
	 */
	public boolean isSane() {
		boolean sane = true;
		for (LassoUnderConstruction luc : m_Lassos_t) {
			sane &= luc.getStem().auxVarsDisjointFromInOutVars();
			sane &= luc.getStem().allAreInOutAux(luc.getStem().getFormula().getFreeVars()) == null;

			sane &= luc.getLoop().auxVarsDisjointFromInOutVars();
			sane &= luc.getLoop().allAreInOutAux(luc.getLoop().getFormula().getFreeVars()) == null;
		}
		
		for (LassoUnderConstruction luc : m_Lassos_nt) {
			sane &= luc.getStem().auxVarsDisjointFromInOutVars();
			sane &= luc.getStem().allAreInOutAux(luc.getStem().getFormula().getFreeVars()) == null;

			sane &= luc.getLoop().auxVarsDisjointFromInOutVars();
			sane &= luc.getLoop().allAreInOutAux(luc.getLoop().getFormula().getFreeVars()) == null;
		}
		return sane;
	}
	
	/**
	 * Extract the overapproximated lassos (for termination analysis)
	 * 
	 * Only succeeds if the transition formulas are of the required form,
	 * i.e., if preprocessing has been completed.
	 * 
	 * @return a colletion of lassos, one for each component
	 * @throws TermException if the transition formulas are not of the correct
	 *                       form
	 */
	public Collection<Lasso> getLassosTermination() throws TermException {
		int n = m_Lassos_t.size();
		List<Lasso> lassos = new ArrayList<Lasso>(n);
		for (int i = 0; i < n; ++i) {
			TransFormulaLR stemTF = m_Lassos_t.get(i).getStem();
			TransFormulaLR loopTF = m_Lassos_t.get(i).getLoop();
			LinearTransition stem = LinearTransition.fromTransFormulaLR(stemTF);
			LinearTransition loop = LinearTransition.fromTransFormulaLR(loopTF);
			lassos.add(new Lasso(stem, loop));
		}
		return lassos;
	}
	
	/**
	 * Extract the underapproximated lassos (for nontermination analysis)
	 * 
	 * Only succeeds if the transition formulas are of the required form,
	 * i.e., if preprocessing has been completed.
	 * 
	 * @return a collection of lassos, one for each component
	 * @throws TermException if the transition formulas are not of the correct
	 *                       form
	 */
	public Collection<Lasso> getLassosNonTermination() throws TermException {
		int n = m_Lassos_nt.size();
		List<Lasso> lassos = new ArrayList<Lasso>(n);
		for (int i = 0; i < n; ++i) {
			TransFormulaLR stemTF = m_Lassos_nt.get(i).getStem();
			TransFormulaLR loopTF = m_Lassos_nt.get(i).getLoop();
			LinearTransition stem = LinearTransition.fromTransFormulaLR(stemTF);
			LinearTransition loop = LinearTransition.fromTransFormulaLR(loopTF);
			lassos.add(new Lasso(stem, loop));
		}
		return lassos;
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		try {
			Collection<Lasso> lassosNonTermination = getLassosNonTermination();
			Collection<Lasso> lassosTermination = getLassosTermination();
			
			sb.append("Overapproximated lassos:\n");
			for (Lasso lasso : lassosTermination) {
				sb.append(lasso);
				sb.append("\n");
			}
			sb.append("Underapproximated lassos:\n");
			for (Lasso lasso : lassosNonTermination) {
				sb.append(lasso);
				sb.append("\n");
			}
		} catch (TermException e) {
			sb.append("Preprocessing has not been completed.\n");
			
			sb.append("Current lassos (overapproximated):\n");
			for (LassoUnderConstruction luc : m_Lassos_t) {
				sb.append(luc);
				sb.append(System.lineSeparator());
			}
			sb.append("Current lassos (underapproximated):\n");
			for (LassoUnderConstruction luc : m_Lassos_t) {
				sb.append(luc);
				sb.append(System.lineSeparator());
			}
		}
		return sb.toString();
	}
	
	public static int computeMaxDagSize(List<LassoUnderConstruction> lassos) {
		if (lassos.isEmpty()) {
			return 0;
		} else {
			int[] sizes = new int[lassos.size()];
			for (int i = 0; i < lassos.size(); ++i) {
				sizes[i] = lassos.get(i).getFormulaSize(); 
			}
			Arrays.sort(sizes);
			return sizes[lassos.size() - 1];
		}
	}
	
	public int computeMaxDagSizeNT() {
		return computeMaxDagSize(m_Lassos_nt);
	}
	
	public int computeMaxDagSizeT() {
		return computeMaxDagSize(m_Lassos_t);
	}

	public void preprocess(LassoPreProcessor[] preProcessorsTermination, LassoPreProcessor[] preProcessorsNontermination) throws TermException {
		m_PreprocessingBenchmark = new PreprocessingBenchmark(
				computeMaxDagSizeNT(), 
				computeMaxDagSizeT());
		// Apply preprocessors
		for (LassoPreProcessor preprocessor : preProcessorsTermination) {
			m_Logger.debug(preprocessor.getDescription());
			applyPreprocessor(preprocessor);
			m_PreprocessingBenchmark.addPreprocessingData(
						preprocessor.getDescription(), 
						computeMaxDagSizeNT(), 
						computeMaxDagSizeT());
			assert isSane() : "lasso failed sanity check";
		}
		
	}

	public PreprocessingBenchmark getPreprocessingBenchmark() {
		return m_PreprocessingBenchmark;
	}
	

}
