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
package de.uni_freiburg.informatik.ultimate.lassoranker;

import java.io.FileNotFoundException;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationArgumentSynthesizer;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.AddAxioms;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.DNF;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.LassoPreProcessor;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.MatchInVars;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RemoveNegation;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteArrays;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteBooleans;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteDivision;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteEquality;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteIte;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteStrictInequalities;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteTrueFalse;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.StemAndLoopPreProcessor;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationArgumentSynthesizer;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.templates.RankingFunctionTemplate;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoBuilder;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoPartitioneer;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;

/**
 * This is the class that controls LassoRanker's (non-)termination analysis
 * 
 * Tools that use LassoRanker as a library probably want to use this class as an
 * interface for invoking LassoRanker. This class can also be derived for a more
 * fine-grained control over the synthesis process.
 * 
 * @author Jan Leike
 */
public class LassoAnalysis {
	private final Logger mLogger;

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
	 * SMT script that created the transition formulae
	 */
	protected final Script m_old_script;

	/**
	 * The axioms regarding the transitions' constants
	 */
	protected final Term[] m_axioms;

	/**
	 * The current preferences
	 */
	protected final LassoRankerPreferences m_preferences;

	/**
	 * Set of terms in which RewriteArrays puts additional supporting invariants
	 */
	protected final Set<Term> m_ArrayIndexSupportingInvariants;

	private final Boogie2SMT m_Boogie2SMT;

	private final IUltimateServiceProvider mServices;

	private final IToolchainStorage mStorage;

	/**
	 * Benchmark data from last termination analysis. 
	 * Includes e.g., the number  of Motzkin's Theorem applications.
	 */
	private LassoTerminationAnalysisBenchmarks m_LassoTerminationAnalysisBenchmarks;

	/**
	 * Constructor for the LassoRanker interface. Calling this invokes the
	 * preprocessor on the stem and loop formula.
	 * 
	 * If the stem is null, the stem has to be added separately by calling
	 * addStem().
	 * 
	 * @param script
	 *            the SMT script used to construct the transition formulae
	 * @param boogie2smt
	 *            the boogie2smt object that created the TransFormula's
	 * @param stem
	 *            a transition formula corresponding to the lasso's stem
	 * @param loop
	 *            a transition formula corresponding to the lasso's loop
	 * @param axioms
	 *            a collection of axioms regarding the transitions' constants
	 * @param preferences
	 *            configuration options for this plugin; these are constant for
	 *            the life time of this object
	 * @param services
	 * @param storage
	 * @throws TermException
	 *             if preprocessing fails
	 * @throws FileNotFoundException
	 *             if the file for dumping the script cannot be opened
	 */
	public LassoAnalysis(Script script, Boogie2SMT boogie2smt, TransFormula stem_transition,
			TransFormula loop_transition, Term[] axioms, LassoRankerPreferences preferences,
			IUltimateServiceProvider services, IToolchainStorage storage) throws TermException {
		
		mServices = services;
		mStorage = storage;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		m_preferences = new LassoRankerPreferences(preferences); // defensive
																	// copy
		m_preferences.checkSanity();
		mLogger.info("Preferences:\n" + m_preferences.toString());
		
		m_old_script = script;
		m_axioms = axioms;
		m_ArrayIndexSupportingInvariants = new HashSet<Term>();
		m_Boogie2SMT = boogie2smt;
		
		m_stem_transition = stem_transition;
		m_loop_transition = loop_transition;
		assert (m_loop_transition != null);
		
		// Preprocessing creates the Lasso object
		m_lasso = this.preprocess();
		
		// This is now a good time to do garbage collection to free the memory
		// allocated during preprocessing. Hopefully it is then available when
		// we call the SMT solver.
		System.gc();
	}

	/**
	 * Constructor for the LassoRanker interface. Calling this invokes the
	 * preprocessor on the stem and loop formula.
	 * 
	 * @param script
	 *            the SMT script used to construct the transition formulae
	 * @param boogie2smt
	 *            the boogie2smt object that created the TransFormulas
	 * @param loop
	 *            a transition formula corresponding to the lasso's loop
	 * @param axioms
	 *            a collection of axioms regarding the transitions' constants
	 * @param preferences
	 *            configuration options for this plugin; these are constant for
	 *            the life time of this object
	 * @param services
	 * @param storage
	 * @throws TermException
	 *             if preprocessing fails
	 * @throws FileNotFoundException
	 *             if the file for dumping the script cannot be opened
	 */
	public LassoAnalysis(Script script, Boogie2SMT boogie2smt, TransFormula loop, Term[] axioms,
			LassoRankerPreferences preferences, IUltimateServiceProvider services, IToolchainStorage storage)
			throws TermException, FileNotFoundException {
		this(script, boogie2smt, null, loop, axioms, preferences, services, storage);
	}
	
	/**
	 * Preprocess the stem or loop transition. This applies the preprocessor
	 * classes and transforms the formula into a list of inequalities in DNF.
	 * 
	 * The list of preprocessors is given by this.getPreProcessors().
	 * 
	 * @see PreProcessor
	 * @throws TermException if preprocessing fails
	 */
	protected Lasso preprocess() throws TermException {
		mLogger.info("Starting lasso preprocessing...");
		LassoBuilder lassoBuilder = new LassoBuilder(m_old_script, m_Boogie2SMT,
				m_stem_transition, m_loop_transition);
		assert lassoBuilder.isSane();
		// Apply preprocessors
		for (LassoPreProcessor preprocessor : this.getPreProcessors(lassoBuilder,
				m_preferences.overapproximateArrayIndexConnection)) {
			mLogger.debug(preprocessor.getDescription());
			preprocessor.process(lassoBuilder);
		}
		
		assert lassoBuilder.isSane();
		
		// Some debug messages
		Lasso lasso = lassoBuilder.getLasso();
		mLogger.debug(new DebugMessage("Stem transition:\n{0}",
				m_stem_transition));
		mLogger.debug(new DebugMessage("Preprocessed stem:\n{0}",
				lasso.getStem()));
		mLogger.debug(new DebugMessage("Loop transition:\n{0}",
				m_loop_transition));
		mLogger.debug(new DebugMessage("Preprocessed loop:\n{0}",
				lasso.getLoop()));
		mLogger.info("Preprocessing complete.");
		mLogger.debug("Guesses for Motzkin coefficients: "
				+ eigenvalueGuesses(lasso));
		
		return lasso;
	}
	
	/**
	 * @param lassoBuilder 
	 * @return an array of all preprocessors that should be called before
	 *         termination analysis
	 */
	protected LassoPreProcessor[] getPreProcessors(
			LassoBuilder lassoBuilder, boolean overapproximateArrayIndexConnection) {
		return new LassoPreProcessor[] {
				new StemAndLoopPreProcessor(new MatchInVars(lassoBuilder.getReplacementVarFactory())),
				new StemAndLoopPreProcessor(new AddAxioms(m_axioms)),
				new LassoPartitioneer(mServices),
				new RewriteArrays(
						m_ArrayIndexSupportingInvariants,
						overapproximateArrayIndexConnection,
						m_stem_transition,
						m_loop_transition,
						mServices
				),
				new StemAndLoopPreProcessor(new RewriteDivision(lassoBuilder.getReplacementVarFactory())),
				new StemAndLoopPreProcessor(new RewriteBooleans(lassoBuilder.getReplacementVarFactory(), lassoBuilder.getScript())),
				new StemAndLoopPreProcessor(new RewriteIte()),
				new StemAndLoopPreProcessor(new RewriteTrueFalse()),
				new StemAndLoopPreProcessor(new RewriteEquality()),
				new StemAndLoopPreProcessor(new DNF(mServices)),
				new StemAndLoopPreProcessor(new RemoveNegation()),
				new StemAndLoopPreProcessor(new RewriteStrictInequalities()),
		};
	}
	
	/**
	 * @return the preprocesses lasso
	 */
	public Lasso getLasso() {
		return m_lasso;
	}
	


	public LassoTerminationAnalysisBenchmarks getLassoTerminationAnalysisBenchmarks() {
		return m_LassoTerminationAnalysisBenchmarks;
	}

	protected String benchmarkScriptMessage(LBool constraintSat, RankingFunctionTemplate template) {
		StringBuilder sb = new StringBuilder();
		sb.append("BenchmarkResult: ");
		sb.append(constraintSat);
		sb.append(" for template ");
		sb.append(template.getName());
		sb.append(" with degree ");
		sb.append(template.getDegree());
		sb.append(". ");
		sb.append(getLassoTerminationAnalysisBenchmarks().toString());
		return sb.toString();
	}

	/**
	 * @return a pretty version of the guesses for loop eigenvalues
	 */
	protected static String eigenvalueGuesses(Lasso lasso) {
		StringBuilder sb = new StringBuilder();
		Rational[] eigenvalues = lasso.guessEigenvalues(true);
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
	 * Try to find a non-termination argument for the lasso program.
	 * 
	 * @param settings
	 *            (local) settings for nontermination analysis
	 * @param services
	 * @return the non-termination argument or null of none is found
	 */
	public NonTerminationArgument checkNonTermination(NonTerminationAnalysisSettings settings) throws SMTLIBException,
			TermException {
		mLogger.info("Checking for nontermination...");

		NonTerminationArgumentSynthesizer nas = new NonTerminationArgumentSynthesizer(m_lasso, m_preferences, settings,
				mServices, mStorage);
		final LBool constraintSat = nas.synthesize();
		if (constraintSat == LBool.SAT) {
			mLogger.info("Proved nontermination.");
			mLogger.info(nas.getArgument());
		}
		nas.close();
		return (constraintSat == LBool.SAT) ? nas.getArgument() : null;
	}

	/**
	 * Try to find a termination argument for the lasso program specified by the
	 * given ranking function template.
	 * 
	 * @param template
	 *            the ranking function template
	 * @param settings
	 *            (local) settings for termination analysis
	 * @return the termination argument or null of none is found
	 */
	public TerminationArgument tryTemplate(RankingFunctionTemplate template, TerminationAnalysisSettings settings)
			throws SMTLIBException, TermException {
		// ignore stem
		mLogger.info("Using template '" + template.getName() + "'.");
		mLogger.info("Template has degree " + template.getDegree() + ".");
		mLogger.debug(template);

		TerminationArgumentSynthesizer tas = new TerminationArgumentSynthesizer(m_lasso, template, m_preferences,
				settings, m_ArrayIndexSupportingInvariants, mServices, mStorage);
		final LBool constraintSat = tas.synthesize();
		if (constraintSat == LBool.SAT) {
			mLogger.info("Proved termination.");
			TerminationArgument arg = tas.getArgument();
			mLogger.info(arg);
			Term[] lexTerm = arg.getRankingFunction().asLexTerm(m_old_script);
			for (Term t : lexTerm) {
				mLogger.debug(new DebugMessage("{0}", new SMTPrettyPrinter(t)));
			}
		}
		m_LassoTerminationAnalysisBenchmarks = new LassoTerminationAnalysisBenchmarks(
				constraintSat, m_lasso.getStemVarNum(), m_lasso.getLoopVarNum(), 
				m_lasso.getStemDisjuncts(), m_lasso.getLoopDisjuncts(), 
				template.getName(), template.getDegree(), 
				tas.getNumSIs(), tas.getNumMotzkin());
		mLogger.debug(benchmarkScriptMessage(constraintSat, template));
		tas.close();
		return (constraintSat == LBool.SAT) ? tas.getArgument() : null;
	}
	
	
	
	public class LassoTerminationAnalysisBenchmarks implements ICsvProviderProvider<Object> {
		private final LBool m_ConstraintsSatisfiability;
		private final int m_VariablesStem;
		private final int m_VariablesLoop;
		private final int m_DisjunctsStem;
		private final int m_DisjunctsLoop;
		private final String m_Template;
		private final int m_Degree;
		private final int m_SupportingInvariants;
		private final int m_MotzkinApplications;
		public LassoTerminationAnalysisBenchmarks(
				LBool constraintsSatisfiability, int variablesStem,
				int variablesLoop, int disjunctsStem, int disjunctsLoop,
				String template, int degree, int supportingInvariants,
				int motzkinApplications) {
			super();
			m_ConstraintsSatisfiability = constraintsSatisfiability;
			m_VariablesStem = variablesStem;
			m_VariablesLoop = variablesLoop;
			m_DisjunctsStem = disjunctsStem;
			m_DisjunctsLoop = disjunctsLoop;
			m_Template = template;
			m_Degree = degree;
			m_SupportingInvariants = supportingInvariants;
			m_MotzkinApplications = motzkinApplications;
		}
		public LBool getConstraintsSatisfiability() {
			return m_ConstraintsSatisfiability;
		}
		public int getVariablesStem() {
			return m_VariablesStem;
		}
		public int getVariablesLoop() {
			return m_VariablesLoop;
		}
		public int getDisjunctsStem() {
			return m_DisjunctsStem;
		}
		public int getDisjunctsLoop() {
			return m_DisjunctsLoop;
		}
		public String getTemplate() {
			return m_Template;
		}
		public int getDegree() {
			return m_Degree;
		}
		public int getSupportingInvariants() {
			return m_SupportingInvariants;
		}
		public int getMotzkinApplications() {
			return m_MotzkinApplications;
		}
		public String toString() {
			StringBuilder sb = new StringBuilder();
//			sb.append("Number of variables in the stem: ");
//			sb.append(getVariablesStem());
//			sb.append("  Number of variables in the loop: ");
//			sb.append(getVariablesLoop());
//			sb.append("  Number of disjunctions in the stem: ");
//			sb.append(getDisjunctsStem());
//			sb.append("  Number of disjunctions in the loop: ");
//			sb.append(getDisjunctsLoop());
//			sb.append("  Number of supporting invariants: ");
//			sb.append(getNumSIs());
//			sb.append("  Number of Motzkin applications: ");
//			sb.append(getNumMotzkin());
			for (Entry<String, Object> entry : getKeyValueMap().entrySet()) {
				sb.append(entry.getKey());
				sb.append(": ");
				sb.append(entry.getValue());
				sb.append("  ");
			}
			return sb.toString();
		}
		
		public Map<String, Object> getKeyValueMap() {
			Map<String, Object> result = new LinkedHashMap<String, Object>();
			result.put("ConstraintsSatisfiability", m_ConstraintsSatisfiability);
			result.put("VariablesStem", m_VariablesStem);
			result.put("VariablesLoop", m_VariablesLoop);
			result.put("DisjunctsStem", m_DisjunctsStem);
			result.put("DisjunctsLoop", m_DisjunctsLoop);
			result.put("SupportingInvariants", m_SupportingInvariants);
			result.put("Template", m_Template);
			result.put("Degree", m_Degree);
			result.put("MotzkinApplications", m_MotzkinApplications);
			return Collections.unmodifiableMap(result);
		}
		@Override
		public ICsvProvider<Object> createCvsProvider() {
			return CsvUtils.constructCvsProviderFromMap(getKeyValueMap());
		}
	}
}