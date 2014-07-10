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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.io.FileNotFoundException;
import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.nontermination.NonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.nontermination.NonTerminationArgumentSynthesizer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.DNF;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.PreProcessor;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.RemoveNegation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.RewriteArrays;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.RewriteBooleans;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.RewriteDivision;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.RewriteEquality;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.RewriteIte;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.RewriteStrictInequalities;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.RewriteTrueFalse;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.termination.TerminationArgument;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.termination.TerminationArgumentSynthesizer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.termination.templates.RankingFunctionTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.variables.VarCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.variables.VarFactory;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;


/**
 * This is the class that controls LassoRanker's (non-)termination analysis
 * 
 * Tools that use LassoRanker as a library probably want to use this class
 * as an interface for invoking LassoRanker. This class can also be derived
 * for a more fine-grained control over the synthesis process.
 * 
 * @author Jan Leike
 */
public class LassoAnalysis {
	private static Logger s_Logger =
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	/**
	 * Stem formula of the linear lasso program
	 */
	private TransFormula m_stem_transition;
	
	/**
	 * Loop formula of the linear lasso program
	 */
	private final TransFormula m_loop_transition;
	
	/**
	 * The lasso program that we are analyzing
	 */
	private Lasso m_lasso;
	
	/**
	 * The RankVarFactory used by the preprocessors and the RankVarCollector
	 */
	private final VarFactory m_rankVarFactory;
	
	/**
	 * SMT script that created the transition formulae
	 */
	protected final Script m_old_script;
	
	/**
	 * The axioms regarding the transitions' constants
	 */
	protected final Term[] m_axioms;
	
	/**
	 * Number of supporting invariants generated by the last termination
	 * analysis
	 */
	private int m_numSIs = 0;
	
	/**
	 * Number of Motzkin's Theorem applications in the last termination
	 * analysis
	 */
	private int m_numMotzkin = 0;
	
	/**
	 * The current preferences
	 */
	protected final Preferences m_preferences;
	
	/**
	 * Set of terms in which RewriteArrays puts additional supporting invariants
	 */
	protected final Set<Term> m_ArrayIndexSupportingInvariants;
	
	private final Boogie2SMT m_Boogie2SMT;
	
	/**
	 * Constructor for the LassoRanker interface. Calling this invokes the
	 * preprocessor on the stem and loop formula.
	 * 
	 * If the stem is null, the stem has to be added separately by calling
	 * addStem().
	 * 
	 * @param script the SMT script used to construct the transition formulae
	 * @param boogie2smt the boogie2smt object that created the TransFormula's
	 * @param stem a transition formula corresponding to the lasso's stem
	 * @param loop a transition formula corresponding to the lasso's loop
	 * @param axioms a collection of axioms regarding the transitions' constants
	 * @param preferences configuration options for this plugin
	 * @throws TermException if preprocessing fails
	 * @throws FileNotFoundException if the file for dumping the script
	 *                               cannot be opened
	 */
	public LassoAnalysis(Script script, Boogie2SMT boogie2smt,
			TransFormula stem_transition, TransFormula loop_transition,
			Term[] axioms, Preferences preferences) throws TermException {
		m_preferences = preferences;
		checkPreferences(preferences);
		m_rankVarFactory = new VarFactory(boogie2smt);
		m_old_script = script;
		m_axioms = axioms;
		m_ArrayIndexSupportingInvariants = new HashSet<Term>();
		m_Boogie2SMT = boogie2smt;
		
		m_stem_transition = stem_transition;
		m_loop_transition = loop_transition;
		assert(m_loop_transition != null);
		
		// Preprocessing creates the Lasso object
		this.do_preprocessing();
	}
	
	/**
	 * Constructor for the LassoRanker interface. Calling this invokes the
	 * preprocessor on the stem and loop formula.
	 *  
	 * This constructor may only be supplied a loop transition, a stem has to
	 * be added later by calling addStem().
	 * 
	 * @param script the SMT script used to construct the transition formulae
	 * @param boogie2smt the boogie2smt object that created the TransFormulas
	 * @param loop a transition formula corresponding to the lasso's loop
	 * @param axioms a collection of axioms regarding the transitions' constants
	 * @param preferences configuration options for this plugin
	 * @throws TermException if preprocessing fails
	 * @throws FileNotFoundException if the file for dumping the script
	 *                               cannot be opened
	 */
	public LassoAnalysis(Script script, Boogie2SMT boogie2smt,
			TransFormula loop, Term[] axioms, Preferences preferences)
					throws TermException, FileNotFoundException {
		this(script, boogie2smt, null, loop, axioms, preferences);
	}
	
	/**
	 * Preprocess the stem and loop transition into a lasso object
	 */
	protected void do_preprocessing() throws TermException {
		LinearTransition stem;
		if (m_stem_transition != null) {
			s_Logger.debug("Stem transition:\n" + m_stem_transition);
			stem = this.preprocess(m_stem_transition, false, null, null);
			s_Logger.debug("Preprocessed stem:\n" + stem);
		} else {
			stem = null;
		}
		
		s_Logger.debug("Loop transition:\n" + m_loop_transition);
		LinearTransition loop = this.preprocess(m_loop_transition, true,
				m_stem_transition, m_loop_transition);
		s_Logger.debug("Preprocessed loop:\n" + loop);
		m_lasso = new Lasso(stem, loop);
		s_Logger.debug("Guesses for Motzkin coefficients: " + motzkinGuesses());
	}
	
	/**
	 * Verify that the preferences are set self-consistent and sensible
	 * Issues a bunch of logger infos and warnings.
	 */
	protected void checkPreferences(Preferences preferences) {
		assert preferences.num_strict_invariants >= 0;
		assert preferences.num_non_strict_invariants >= 0;
//		assert preferences.termination_check_nonlinear
//				|| preferences.only_nondecreasing_invariants
//				: "Use nondecreasing invariants with a linear SMT query.";
		if (preferences.num_strict_invariants == 0 &&
				preferences.num_non_strict_invariants == 0) {
			s_Logger.warn("Generation of supporting invariants is disabled.");
		}
	}
	
	/**
	 * @param rvc the ranking variable collector to be passed to the
	 *        preprocessors
	 * @return an array of all preprocessors that should be called before
	 *         termination analysis
	 */
	protected PreProcessor[] getPreProcessors(VarCollector rvc,
			boolean searchArrayIndexSupportingInvariants,
			TransFormula stem, TransFormula loop,
			boolean overapproximateArrayIndexConnection) {
		return new PreProcessor[] {
				new RewriteArrays(rvc, searchArrayIndexSupportingInvariants,
						stem, loop, m_Boogie2SMT, 
						m_ArrayIndexSupportingInvariants, 
						overapproximateArrayIndexConnection),
				new RewriteDivision(rvc),
				new RewriteBooleans(rvc),
				new RewriteIte(),
				new RewriteTrueFalse(),
				new RewriteEquality(),
				new DNF(),
				new RemoveNegation(),
				new RewriteStrictInequalities()
		};
	}
	
	/**
	 * Preprocess the stem or loop transition. This applies the preprocessor
	 * classes and transforms the formula into a list of inequalities in DNF.
	 * 
	 * The list of preprocessors is given by this.getPreProcessors().
	 * 
	 * @see PreProcessor
	 * @throws TermException
	 */
	protected LinearTransition preprocess(TransFormula transition,
			boolean searchArrayIndexSupportingInvariants,
			TransFormula originalStem, TransFormula originalLoop)
			throws TermException {
		s_Logger.info("Starting preprocessing step...");
		
		Term trans_term = transition.getFormula();
		Term axioms = Util.and(m_old_script, m_axioms);
		trans_term = Util.and(m_old_script, trans_term, axioms);
		VarCollector rvc =
				new VarCollector(m_rankVarFactory, transition);
		assert rvc.auxVarsDisjointFromInOutVars();
		assert rvc.allAreInOutAux(trans_term.getFreeVars()) == null;
		
		// Apply preprocessors
		for (PreProcessor preprocessor : this.getPreProcessors(rvc, 
				searchArrayIndexSupportingInvariants, originalStem, originalLoop,
				m_preferences.overapproximateArrayIndexConnection)) {
			trans_term = preprocessor.process(m_old_script, trans_term);
		}
		
		assert rvc.auxVarsDisjointFromInOutVars();
		assert rvc.allAreInOutAux(trans_term.getFreeVars()) == null;
		
		s_Logger.debug(new DebugMessage("{0}", new SMTPrettyPrinter(trans_term)));
		
		// Match inVars
		rvc.matchInVars();
		
		LinearTransition linear_trans = LinearTransition.fromTerm(
				trans_term, rvc.getInVars(), rvc.getOutVars());
		
		return linear_trans;
	}
	
	/**
	 * @return the preprocesses lasso
	 */
	public Lasso getLasso() {
		return m_lasso;
	}
	
	/**
	 * @return the number of variables occurring in the preprocessed loop
	 *         transition
	 */
	public int getLoopVarNum() {
		return m_lasso.getLoop().getVariables().size();
	}
	
	/**
	 * @return the number of variables occurring in the preprocessed stem
	 *         transition
	 */
	public int getStemVarNum() {
		return m_lasso.getStem().getVariables().size();
	}
	
	/**
	 * @return the number of disjuncts in the loop transition's DNF after
	 *         preprocessing
	 */
	public int getLoopDisjuncts() {
		return m_lasso.getLoop().getNumPolyhedra();
	}
	
	/**
	 * @return the number of disjuncts in the stem transition's DNF after
	 *         preprocessing
	 */
	public int getStemDisjuncts() {
		return m_lasso.getStem().getNumPolyhedra();
	}
	
	/**
	 * @return the number of supporting invariants generated by the last
	 * termination analysis
	 */
	public int getNumSIs() {
		return m_numSIs;
	}
	
	/**
	 * @return the number of Motzkin's Theorem applications in the last
	 * termination analysis
	 */
	public int getNumMotzkin() {
		return m_numMotzkin;
	}
	
	protected String benchmarkScriptMessage(LBool constraintSat,
			RankingFunctionTemplate template) {
		StringBuilder sb = new StringBuilder();
		sb.append("BenchmarkResult: ");
		sb.append(constraintSat);
		sb.append(" for template ");
		sb.append(template.getName());
		sb.append(" with degree ");
		sb.append(template.getDegree());
		sb.append(". ");
		sb.append(getStatistics());
		return sb.toString();
	}
	
	/**
	 * @return a pretty version of the guesses for Motzkin coefficients
	 */
	protected String motzkinGuesses() {
		StringBuilder sb = new StringBuilder();
		Rational[] eigenvalues = m_lasso.guessEigenvalues(true);
		sb.append("[");
		for (int i = 0; i < eigenvalues.length; ++i) {
			if (i > 0) {
				sb.append(", ");
			}
			sb.append(eigenvalues[i].toString());
		}
		sb.append("]");
		return sb.toString();
	}
	
	/**
	 * @return various statistics as a neatly formatted string
	 */
	public String getStatistics() {
		StringBuilder sb = new StringBuilder();
		sb.append("Number of variables in the stem: ");
		sb.append(getStemVarNum());
		sb.append("  Number of variables in the loop: ");
		sb.append(getLoopVarNum());
		sb.append("  Number of disjunctions in the stem: ");
		sb.append(getStemDisjuncts());
		sb.append("  Number of disjunctions in the loop: ");
		sb.append(getLoopDisjuncts());
		sb.append("  Number of supporting invariants: ");
		sb.append(getNumSIs());
		sb.append("  Number of Motzkin applications: ");
		sb.append(getNumMotzkin());
		return sb.toString();
	}
	
	/**
	 * Try to find a non-termination argument for the lasso program.
	 * 
	 * @return the non-termination argument or null of none is found
	 */
	public NonTerminationArgument checkNonTermination()
			throws SMTLIBException, TermException {
		s_Logger.info("Checking for nontermination...");
		
		NonTerminationArgumentSynthesizer nas =
				new NonTerminationArgumentSynthesizer(m_lasso, m_preferences);
		final LBool constraintSat = nas.synthesize();
		if (constraintSat == LBool.SAT) {
			s_Logger.info("Proved nontermination.");
			s_Logger.info(nas.getArgument());
		}
		nas.close();
		return (constraintSat == LBool.SAT) ? nas.getArgument() : null;
	}
	
	/**
	 * Try to find a termination argument for the lasso program specified by
	 * the given ranking function template.
	 * 
	 * @param template the ranking function template
	 * @return the termination argument or null of none is found
	 */
	public TerminationArgument tryTemplate(RankingFunctionTemplate template)
			throws SMTLIBException, TermException {
		// ignore stem
		s_Logger.info("Using template '" + template.getName()
				+ "'.");
		s_Logger.info("Template has degree " + template.getDegree() + ".");
		s_Logger.debug(template);
		
		TerminationArgumentSynthesizer tas =
				new TerminationArgumentSynthesizer(m_lasso, template,
						m_preferences, m_ArrayIndexSupportingInvariants);
		final LBool constraintSat = tas.synthesize();
		m_numSIs = tas.getNumSIs();
		m_numMotzkin = tas.getNumMotzkin();
		s_Logger.debug(benchmarkScriptMessage(constraintSat, template));
		if (constraintSat == LBool.SAT) {
			s_Logger.info("Proved termination.");
			TerminationArgument arg = tas.getArgument();
			s_Logger.info(arg);
			Term[] lexTerm = arg.getRankingFunction().asLexTerm(m_old_script);
			for (Term t : lexTerm) {
				s_Logger.debug(new DebugMessage("{0}", new SMTPrettyPrinter(t)));
			}
		}
		tas.close();
		return (constraintSat == LBool.SAT) ? tas.getArgument() : null;
	}
}
