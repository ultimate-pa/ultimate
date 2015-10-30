/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE LassoRanker plug-in.
 * 
 * The ULTIMATE LassoRanker plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LassoRanker plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE LassoRanker plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.model.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.services.model.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;
import de.uni_freiburg.informatik.ultimate.lassoranker.BacktranslationUtil;
import de.uni_freiburg.informatik.ultimate.lassoranker.LassoAnalysis;
import de.uni_freiburg.informatik.ultimate.lassoranker.LassoRankerPreferences;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.SupportingInvariant;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.templates.AffineTemplate;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.templates.ComposableTemplate;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.templates.ComposedLexicographicTemplate;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.templates.LexicographicTemplate;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.templates.MultiphaseTemplate;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.templates.NestedTemplate;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.templates.ParallelTemplate;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.templates.PiecewiseTemplate;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.templates.RankingTemplate;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.RankVar;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Term2Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BinaryStatePredicateManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer.CodeBlockSize;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.NoResult;
import de.uni_freiburg.informatik.ultimate.result.NonTerminationArgumentResult;
import de.uni_freiburg.informatik.ultimate.result.TerminationArgumentResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.result.UnsupportedSyntaxResult;

/**
 * Takes the root node of an RCFG, extracts a lasso and analyzes its
 * termination.
 * 
 * @author Matthias Heizmann, Jan Leike
 */
public class LassoRankerStarter {
	private final Logger mLogger;
	private static final String s_LassoError = "This is not a lasso program (a lasso program is a program "
			+ "consisting of a stem and a loop transition)";

	private final RootAnnot m_RootAnnot;
	private final ProgramPoint m_Honda;
	private final NestedWord<CodeBlock> m_Stem;
	private final NestedWord<CodeBlock> m_Loop;
	private SmtManager m_SmtManager;
	private final IUltimateServiceProvider mServices;

	public LassoRankerStarter(RootNode rootNode, IUltimateServiceProvider services, IToolchainStorage storage)
			throws IOException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);

		m_RootAnnot = rootNode.getRootAnnot();
		// Omit check to enable Stefans BlockEncoding
		// checkRCFGBuilderSettings();
		LassoRankerPreferences preferences = PreferencesInitializer.getLassoRankerPreferences();
		m_SmtManager = new SmtManager(m_RootAnnot.getScript(), m_RootAnnot.getBoogie2SMT(), m_RootAnnot.getModGlobVarManager(), mServices, false);

		AbstractLassoExtractor lassoExtractor;
		boolean useNewExtraction = true;
		if (useNewExtraction) {
			try {
				lassoExtractor = new LassoExtractorBuchi(mServices, rootNode, m_SmtManager, mLogger);
			} catch (OperationCanceledException oce) {
				throw new AssertionError("timeout while searching lasso");
//				throw new ToolchainCanceledException(this.getClass());
			} catch (AutomataLibraryException e) {
				throw new AssertionError(e.toString());
			}
		} else {
			lassoExtractor = new LassoExtractorNaive(rootNode);
		}
		if (!lassoExtractor.wasLassoFound()) {
			reportUnuspportedSyntax(lassoExtractor.getSomeNoneForErrorReport(), s_LassoError);
			m_Stem = null;
			m_Loop = null;
			m_Honda = null;
			return;
		}
		m_Stem = lassoExtractor.getStem();
		m_Loop = lassoExtractor.getLoop();
		m_Honda = lassoExtractor.getHonda();

		Script script = m_RootAnnot.getScript();

		TermVariableRenamer tvr = new TermVariableRenamer(script);
		TransFormula stemTF;
		if (m_Stem == null) {
			stemTF = null;
		} else {
			stemTF = constructTransformula(m_Stem);
			stemTF = tvr.renameVars(stemTF, "Stem");
		}
		TransFormula loopTf = constructTransformula(m_Loop);
		loopTf = tvr.renameVars(loopTf, "Loop");

		Term[] axioms = m_RootAnnot.getBoogie2SMT().getAxioms().toArray(new Term[0]);
		Set<BoogieVar> modifiableGlobalsAtHonda = 
				m_RootAnnot.getModGlobVarManager().getModifiedBoogieVars(m_Honda.getProcedure());

		// Construct LassoAnalysis for nontermination
		LassoAnalysis laNT = null;
		try {
			laNT = new LassoAnalysis(script, m_RootAnnot.getBoogie2SMT(), stemTF, loopTf, 
					modifiableGlobalsAtHonda, axioms, preferences, mServices,
					storage);
		} catch (TermException e) {
			reportUnuspportedSyntax(m_Honda, e.getMessage());
			return;
		}

		// Try to prove non-termination
		NonTerminationAnalysisSettings nontermination_settings = PreferencesInitializer
				.getNonTerminationAnalysisSettings();
		if (nontermination_settings.analysis != AnalysisType.Disabled) {
			try {
				NonTerminationArgument nta =
						laNT.checkNonTermination(nontermination_settings);
				if (nta != null) {
					if (!lassoWasOverapproximated().isEmpty()) {
						reportFailBecauseOfOverapproximationResult();
						return;
					}
					reportNonTerminationResult(nta);
					return;
				}
			} catch (SMTLIBException e) {
				mLogger.error(e);
			} catch (TermException e) {
				mLogger.error(e);
			}
		}

		TerminationAnalysisSettings termination_settings = PreferencesInitializer.getTerminationAnalysisSettings();

		// Construct LassoAnalysis for nontermination
		LassoAnalysis laT = null;
		try {
			laT = new LassoAnalysis(script, m_RootAnnot.getBoogie2SMT(), stemTF, loopTf, 
					modifiableGlobalsAtHonda, axioms, preferences, mServices,
					storage);
		} catch (TermException e) {
			reportUnuspportedSyntax(m_Honda, e.getMessage());
			return;
		}
		
		// Get all templates
		RankingTemplate[] templates;
		if (termination_settings.analysis == AnalysisType.Disabled) {
			templates = new RankingTemplate[0];
		} else {
			templates = getTemplates();
		}
		// Do the termination analysis
		for (RankingTemplate template : templates) {
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				reportTimeoutResult(templates, template);
				// Timeout or abort
				return;
			}
			try {
				TerminationArgument arg = laT.tryTemplate(template, termination_settings);
				if (arg != null) {
					// try {
					assert isTerminationArgumentCorrect(arg, stemTF, loopTf) : "Incorrect termination argument from"
							+ template.getClass().getSimpleName();
					// } catch (NoClassDefFoundError e) {
					// s_Logger.warn("Could not check validity of " +
					// "termination argument because of " +
					// "missing dependencies.");
					// // Requires: BuchiAutomizer, TraceAbstraction,
					// // NestedWordAutomata
					// }
					reportTerminationResult(arg);
					return;
				}
			} catch (TermException e) {
				mLogger.error(e);
				throw new AssertionError(e);
			} catch (SMTLIBException e) {
				mLogger.error(e);
				throw new AssertionError(e);
			}
		}
		reportNoResult(templates);
	}
	
	private Map<String, ILocation> lassoWasOverapproximated() {
		Map<String, ILocation> overapproximations = new HashMap<>();
		overapproximations.putAll(RcfgProgramExecution.getOverapproximations(m_Stem.asList()));
		overapproximations.putAll(RcfgProgramExecution.getOverapproximations(m_Loop.asList()));
		return overapproximations;
	}

	public TransFormula constructTransformula(NestedWord<CodeBlock> nw) {
		Boogie2SMT boogie2smt = m_RootAnnot.getBoogie2SMT();
		ModifiableGlobalVariableManager modGlobVarManager = m_RootAnnot.getModGlobVarManager();
		boolean simplify = true;
		boolean extPqe = true;
		boolean tranformToCNF = false;
		boolean withBranchEncoders = false;
		List<CodeBlock> codeBlocks = Collections.unmodifiableList(nw.asList());
		return SequentialComposition.getInterproceduralTransFormula(boogie2smt, modGlobVarManager, simplify, extPqe,
				tranformToCNF, withBranchEncoders, mLogger, mServices, codeBlocks);
	}

	/**
	 * Build a list of templates. Add all templates from size 2 up to the given
	 * size.
	 * 
	 * @param preferences
	 * @return the templates specified in the preferences
	 */
	private RankingTemplate[] getTemplates() {
		UltimatePreferenceStore store = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		List<RankingTemplate> templates = new ArrayList<RankingTemplate>();

		if (store.getBoolean(PreferencesInitializer.LABEL_enable_affine_template)) {
			templates.add(new AffineTemplate());
		}
		if (store.getBoolean(PreferencesInitializer.LABEL_enable_nested_template)) {
			int maxSize = store.getInt(PreferencesInitializer.LABEL_nested_template_size);
			for (int i = 2; i <= maxSize; i++) {
				templates.add(new NestedTemplate(i));
			}
		}
		if (store.getBoolean(PreferencesInitializer.LABEL_enable_multiphase_template)) {
			int maxSize = store.getInt(PreferencesInitializer.LABEL_multiphase_template_size);
			for (int i = 2; i <= maxSize; i++) {
				templates.add(new MultiphaseTemplate(i));
			}
		}
		if (store.getBoolean(PreferencesInitializer.LABEL_enable_lex_template)) {
			int maxSize = store.getInt(PreferencesInitializer.LABEL_lex_template_size);
			for (int i = 2; i <= maxSize; i++) {
				AffineTemplate[] parts = new AffineTemplate[i];
				for (int j = 0; j < i; ++j) {
					parts[j] = new AffineTemplate();
				}
				templates.add(new ComposedLexicographicTemplate(parts));
			}
		}
		if (store.getBoolean(PreferencesInitializer.LABEL_enable_piecewise_template)) {
			int maxSize = store.getInt(PreferencesInitializer.LABEL_piecewise_template_size);
			for (int i = 2; i <= maxSize; i++) {
				templates.add(new PiecewiseTemplate(i));
			}
		}
		if (store.getBoolean(PreferencesInitializer.LABEL_enable_parallel_template)) {
			int maxSize = store.getInt(PreferencesInitializer.LABEL_parallel_template_size);
			for (int i = 2; i <= maxSize; i++) {
				templates.add(new ParallelTemplate(i));
			}
		}
		if (store.getBoolean(PreferencesInitializer.LABEL_enable_multilex_template)) {
			int maxSize = store.getInt(PreferencesInitializer.LABEL_multilex_template_size);
			for (int i = 2; i <= maxSize; i++) {
				ComposableTemplate[] parts = new ComposableTemplate[i];
				for (int j = 0; j < i; ++j) {
					parts[j] = new MultiphaseTemplate(i);
				}
				templates.add(new ComposedLexicographicTemplate(parts));
			}
		}
		return templates.toArray(new RankingTemplate[0]);
	}

	/**
	 * Build a list of templates. Add all templates with exactly the given size.
	 * 
	 * @param preferences
	 * @return the templates specified in the preferences
	 */
	private RankingTemplate[] getTemplatesExactly() {
		UltimatePreferenceStore store = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		List<RankingTemplate> templates = new ArrayList<RankingTemplate>();

		if (store.getBoolean(PreferencesInitializer.LABEL_enable_affine_template)) {
			templates.add(new AffineTemplate());
		}
		if (store.getBoolean(PreferencesInitializer.LABEL_enable_nested_template)) {
			templates.add(new NestedTemplate(store.getInt(PreferencesInitializer.LABEL_nested_template_size)));
		}
		if (store.getBoolean(PreferencesInitializer.LABEL_enable_multiphase_template)) {
			templates.add(new MultiphaseTemplate(store.getInt(PreferencesInitializer.LABEL_multiphase_template_size)));
		}
		if (store.getBoolean(PreferencesInitializer.LABEL_enable_lex_template)) {
			templates.add(new LexicographicTemplate(store.getInt(PreferencesInitializer.LABEL_lex_template_size)));
		}
		if (store.getBoolean(PreferencesInitializer.LABEL_enable_piecewise_template)) {
			templates.add(new PiecewiseTemplate(store.getInt(PreferencesInitializer.LABEL_piecewise_template_size)));
		}
		if (store.getBoolean(PreferencesInitializer.LABEL_enable_parallel_template)) {
			templates.add(new ParallelTemplate(store.getInt(PreferencesInitializer.LABEL_parallel_template_size)));
		}
		return templates.toArray(new RankingTemplate[0]);
	}

	private boolean isTerminationArgumentCorrect(TerminationArgument arg, TransFormula stemTF, TransFormula loopTf) {

		BinaryStatePredicateManager bspm = new BinaryStatePredicateManager(m_SmtManager, mServices);
		Set<BoogieVar> modifiableGlobals = m_RootAnnot.getModGlobVarManager().getModifiedBoogieVars(m_Honda.getProcedure());
		bspm.computePredicates(false, arg, false, stemTF, loopTf, modifiableGlobals);

		// check supporting invariants
		boolean siCorrect = true;
		for (SupportingInvariant si : bspm.getTerminationArgument().getSupportingInvariants()) {
			IPredicate siPred = bspm.supportingInvariant2Predicate(si);
			siCorrect &= bspm.checkSupportingInvariant(siPred, m_Stem, m_Loop, m_RootAnnot.getModGlobVarManager());
		}

		// check array index supporting invariants
		for (Term aisi : bspm.getTerminationArgument().getArrayIndexSupportingInvariants()) {
			IPredicate siPred = bspm.term2Predicate(aisi);
			siCorrect &= bspm.checkSupportingInvariant(siPred, m_Stem, m_Loop, m_RootAnnot.getModGlobVarManager());
		}

		// check ranking function
		boolean rfCorrect = bspm.checkRankDecrease(m_Loop, m_RootAnnot.getModGlobVarManager());
		if (siCorrect && rfCorrect) {
			mLogger.info("Termination argument has been successfully verified.");
		}
		return siCorrect && rfCorrect;
	}

	/**
	 * @return the current translator sequence for building results
	 */
	private IBacktranslationService getTranslatorSequence() {
		return mServices.getBacktranslationService();
	}

	/**
	 * Report a termination argument back to Ultimate's toolchain.
	 * 
	 * @param arg
	 *            the termination argument
	 */
	private void reportTerminationResult(TerminationArgument arg) {
		RankingFunction rf = arg.getRankingFunction();
		Collection<SupportingInvariant> si_list = arg.getSupportingInvariants();

		Script script = m_RootAnnot.getScript();
		Term2Expression term2expression = m_RootAnnot.getBoogie2SMT().getTerm2Expression();

		Expression[] supporting_invariants = new Expression[si_list.size()];
		int i = 0;
		for (SupportingInvariant si : si_list) {
			supporting_invariants[i] = si.asExpression(script, term2expression);
			++i;
		}

		TerminationArgumentResult<RcfgElement> result = new TerminationArgumentResult<RcfgElement>(m_Honda,
				Activator.s_PLUGIN_NAME, rf.asLexExpression(script, term2expression), rf.getName(),
				supporting_invariants, getTranslatorSequence());
		reportResult(result);
	}

	/**
	 * Report a nontermination argument back to Ultimate's toolchain
	 * 
	 * @param arg
	 */
	private void reportNonTerminationResult(NonTerminationArgument nta) {
		// TODO: translate also the rational coefficients to Expressions?
		// m_RootAnnot.getBoogie2Smt().translate(term)
		Term2Expression term2expression = m_RootAnnot.getBoogie2SMT().getTerm2Expression();
		
		List<Map<RankVar, Rational>> states =
				new ArrayList<Map<RankVar, Rational>>();
		states.add(nta.getStateInit());
		states.add(nta.getStateHonda());
		states.addAll(nta.getGEVs());
		List<Map<Expression, Rational>> initHondaRays =
				BacktranslationUtil.rank2Boogie(term2expression, states);
		
		NonTerminationArgumentResult<RcfgElement> result =
				new NonTerminationArgumentResult<RcfgElement>(m_Honda,
				Activator.s_PLUGIN_NAME, initHondaRays.get(0),
				initHondaRays.get(1),
				initHondaRays.subList(2, initHondaRays.size()),
				nta.getLambdas(),
				nta.getNus(),
				getTranslatorSequence());
		reportResult(result);
	}

	/**
	 * Report that no result has been found to Ultimate's toolchain
	 * 
	 * @param preferences
	 *            the current preferences
	 */
	private void reportNoResult(RankingTemplate[] templates) {
		NoResult<RcfgElement> result = new NoResult<RcfgElement>(m_Honda, Activator.s_PLUGIN_NAME,
				getTranslatorSequence());
		result.setShortDescription("LassoRanker could not prove termination");
		StringBuilder sb = new StringBuilder();
		sb.append("LassoRanker could not prove termination " + "or nontermination of the given linear lasso program.\n");
		sb.append("Templates:");
		for (RankingTemplate template : templates) {
			sb.append(" ");
			sb.append(template.getClass().getSimpleName());
		}
		result.setLongDescription(sb.toString());
		mLogger.info(sb.toString());
		reportResult(result);
	}
	
	/**
	 * Report that no result has been found and that the reason might be
	 * that the lasso was overapproximated. 
	 * 
	 * @param preferences
	 *            the current preferences
	 */
	private void reportFailBecauseOfOverapproximationResult() {
		NoResult<RcfgElement> result = new NoResult<RcfgElement>(m_Honda, Activator.s_PLUGIN_NAME,
				getTranslatorSequence());
		result.setShortDescription("LassoRanker could not prove termination");
		StringBuilder sb = new StringBuilder();
		sb.append("LassoRanker could not prove termination " + "or nontermination of the given linear lasso program.\n");
		sb.append("The reason might be that LassoRanker had to use an overapproximation of the original lasso.");
		result.setLongDescription(sb.toString());
		mLogger.info(sb.toString());
		reportResult(result);
	}

	/**
	 * Report that there was a timeout. TODO: which templates already failed,
	 * where did the timeout occur.
	 */
	private void reportTimeoutResult(RankingTemplate[] templates, RankingTemplate templateWhereTimeoutOccurred) {
		StringBuilder sb = new StringBuilder();
		sb.append("LassoRanker could not prove termination " + "or nontermination of the given linear lasso program.\n");
		sb.append("Templates:");
		for (RankingTemplate template : templates) {
			sb.append(" ");
			sb.append(template.getClass().getSimpleName());
		}
		TimeoutResultAtElement<RcfgElement> result = new TimeoutResultAtElement<RcfgElement>(m_Honda,
				Activator.s_PLUGIN_NAME, getTranslatorSequence(), sb.toString());
		mLogger.info(sb.toString());
		reportResult(result);
	}

	/**
	 * Report that unsupported syntax was discovered
	 * 
	 * @param position
	 *            the program point
	 * @param message
	 *            an error message explaining the problem
	 */
	private void reportUnuspportedSyntax(RcfgElement position, String message) {
		mLogger.error(message);
		UnsupportedSyntaxResult<RcfgElement> result = new UnsupportedSyntaxResult<RcfgElement>(position,
				Activator.s_PLUGIN_NAME, getTranslatorSequence(), message);
		reportResult(result);
	}
	
	

	/**
	 * Report a result back to the Ultimate toolchain
	 * 
	 * @param result
	 *            the result
	 */
	private void reportResult(IResult result) {
		mServices.getResultService().reportResult(Activator.s_PLUGIN_ID, result);
	}

	// FIXME: allow also Stefans BlockEncoding
	private void checkRCFGBuilderSettings() {
		String rcfgBuilderPluginId = de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator.PLUGIN_ID;
		UltimatePreferenceStore store = new UltimatePreferenceStore(rcfgBuilderPluginId);
		String removeGotoLabel = de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer.LABEL_RemoveGotoEdges;
		boolean removeGoto = store.getBoolean(removeGotoLabel);
		String codeBlockSizeLabel = de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer.LABEL_CodeBlockSize;
		Class<CodeBlockSize> cbsClass = de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer.CodeBlockSize.class;
		CodeBlockSize codeBlockSize = store.getEnum(codeBlockSizeLabel, cbsClass);
		if (codeBlockSize != CodeBlockSize.LoopFreeBlock) {
			throw new UnsupportedOperationException(
					"Unsupported input: Use the large block encoding of the RCFGBuilder");
		}
		if (!removeGoto) {
			throw new UnsupportedOperationException("Unsupported input: Let RCFGBuilder remove goto edges");
		}
	}

}
