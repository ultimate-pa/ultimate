package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;
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
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Term2Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BinaryStatePredicateManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceInitializer.CodeBlockSize;
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

	public LassoRankerStarter(RootNode rootNode, IUltimateServiceProvider services, IToolchainStorage storage) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);

		m_RootAnnot = rootNode.getRootAnnot();
		// Omit check to enable Stefans BlockEncoding
		// checkRCFGBuilderSettings();
		LassoRankerPreferences preferences = PreferencesInitializer.getLassoRankerPreferences();
		m_SmtManager = new SmtManager(m_RootAnnot.getBoogie2SMT(), m_RootAnnot.getModGlobVarManager(), mServices);

		AbstractLassoExtractor lassoExtractor;
		boolean useNewExtraction = true;
		if (useNewExtraction) {
			try {
				lassoExtractor = new LassoExtractorBuchi(rootNode, m_SmtManager, mLogger);
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

		// Do the termination analysis
		LassoAnalysis la = null;
		try {
			la = new LassoAnalysis(script, m_RootAnnot.getBoogie2SMT(), stemTF, loopTf, axioms, preferences, mServices,
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
				NonTerminationArgument arg = la.checkNonTermination(nontermination_settings);
				if (arg != null) {
					reportNonTerminationResult(arg);
					return;
				}
			} catch (SMTLIBException e) {
				mLogger.error(e);
			} catch (TermException e) {
				mLogger.error(e);
			}
		}

		TerminationAnalysisSettings termination_settings = PreferencesInitializer.getTerminationAnalysisSettings();

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
				TerminationArgument arg = la.tryTemplate(template, termination_settings);
				if (arg != null) {
					// try {
					assert isTerminationArgumentCorrect(arg) : "Incorrect termination argument from"
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

	public TransFormula constructTransformula(NestedWord<CodeBlock> nw) {
		Boogie2SMT boogie2smt = m_RootAnnot.getBoogie2SMT();
		ModifiableGlobalVariableManager modGlobVarManager = m_RootAnnot.getModGlobVarManager();
		boolean simplify = true;
		boolean extPqe = true;
		boolean tranformToCNF = false;
		boolean withBranchEncoders = false;
		CodeBlock[] codeBlocks = nw.asList().toArray(new CodeBlock[0]);
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

	private boolean isTerminationArgumentCorrect(TerminationArgument arg) {

		BinaryStatePredicateManager bspm = new BinaryStatePredicateManager(m_SmtManager, mServices);
		bspm.computePredicates(false, arg);

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
	private void reportNonTerminationResult(NonTerminationArgument arg) {
		// TODO: translate also the rational coefficients to Expressions?
		// m_RootAnnot.getBoogie2Smt().translate(term)
		Term2Expression term2expression = m_RootAnnot.getBoogie2SMT().getTerm2Expression();

		List<Map<Expression, Rational>> initHondaRay = NonTerminationArgument.rank2Boogie(term2expression,
				arg.getStateInit(), arg.getStateHonda(), arg.getRay());

		NonTerminationArgumentResult<RcfgElement> result = new NonTerminationArgumentResult<RcfgElement>(m_Honda,
				Activator.s_PLUGIN_NAME, initHondaRay.get(0), initHondaRay.get(1), initHondaRay.get(2),
				arg.getLambda(), getTranslatorSequence());
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
	 * Report that there was a timeout. TODO: which templates already failed,
	 * where did the timeout occur.
	 */
	private void reportTimeoutResult(RankingTemplate[] templates,
			RankingTemplate templateWhereTimeoutOccurred) {
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
		String removeGotoLabel = de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceInitializer.LABEL_RemoveGotoEdges;
		boolean removeGoto = store.getBoolean(removeGotoLabel);
		String codeBlockSizeLabel = de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceInitializer.LABEL_CodeBlockSize;
		Class<CodeBlockSize> cbsClass = de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceInitializer.CodeBlockSize.class;
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
