package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Term2Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates.AffineTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates.LexicographicTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates.MultiphaseTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates.NestedTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates.PiecewiseTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates.RankingFunctionTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BinaryStatePredicateManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
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
	private static Logger s_Logger =
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	private static final String s_LassoError =
			"This is not a lasso program (a lasso program is a program " +
			"consisting of a stem and a loop transition)";

	private final RootAnnot m_RootAnnot;
	private final ProgramPoint m_Honda;
	private final CodeBlock m_Stem;
	private final CodeBlock m_Loop;

	
	
	public LassoRankerStarter(RootNode rootNode) {
		m_RootAnnot = rootNode.getRootAnnot();
		checkRCFGBuilderSettings();
		UltimatePreferenceStore store =
				new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		Preferences preferences = PreferencesInitializer.getGuiPreferences();
		s_Logger.info("Preferences:\n" + preferences.toString());
		
		LassoExtractorNaive lassoExtractor = new LassoExtractorNaive(rootNode);
		if (!lassoExtractor.wasLassoFound()) {
			reportUnuspportedSyntax(
					lassoExtractor.getSomeNoneForErrorReport(), s_LassoError);
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
			stemTF = tvr.renameVars(m_Stem.getTransitionFormula(), "Stem");
		}
		TransFormula loopTf = tvr.renameVars(m_Loop.getTransitionFormula(), "Loop");
		
		// Do the termination analysis
		RankingFunctionTemplate[] templates = getTemplates();
		LassoRankerTerminationAnalysis tanalysis = null;
		try {
			tanalysis = new LassoRankerTerminationAnalysis(script,
					m_RootAnnot.getBoogie2SMT(),
					stemTF, loopTf, preferences);
		} catch (TermException e) {
			reportUnuspportedSyntax(m_Honda, e.getMessage());
			return;
		}
		
		// Try to prove non-termination
		if (store.getBoolean(PreferencesInitializer.LABEL_check_for_nontermination)) {
			try {
				NonTerminationArgument arg = tanalysis.checkNonTermination();
				if (arg != null) {
					reportNonTerminationResult(arg);
					return;
				}
			} catch (SMTLIBException e) {
				s_Logger.error(e);
			} catch (TermException e) {
				s_Logger.error(e);
			}
		}
		
		// Try all given templates
		for (RankingFunctionTemplate template : templates) {
			if (!UltimateServices.getInstance().continueProcessing()) {
				reportTimeoutResult(templates, template);
				// Timeout or abort
				return;
			}
			try {
				TerminationArgument arg = tanalysis.tryTemplate(template);
				if (arg != null) {
					try {
						assert isTerminationArgumentCorrect(arg) : 
							"Incorrect termination argument from" + 
								template.getClass().getSimpleName();
					} catch (NoClassDefFoundError e) {
						s_Logger.warn("Could not check validity of " +
								"termination argument because of " +
								"missing dependencies.");
						// Requires: BuchiAutomizer, TraceAbstraction,
						//           NestedWordAutomata
					}
					reportTerminationResult(arg);
					return;
				}
			} catch (TermException e) {
				s_Logger.error(e);
			} catch (SMTLIBException e) {
				s_Logger.error(e);
			}
		}
		reportNoResult(templates);
	}
	
	
	
	
	
	
	
	/**
	 * Build a list of templates. Add all templates from size 2 up to the given
	 * size.
	 * @param preferences
	 * @return the templates specified in the preferences
	 */
	private RankingFunctionTemplate[] getTemplates() {
		UltimatePreferenceStore store =
				new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		List<RankingFunctionTemplate> templates =
				new ArrayList<RankingFunctionTemplate>();
		
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
		if (store.getBoolean(PreferencesInitializer.LABEL_enable_piecewise_template)) {
			int maxSize = store.getInt(PreferencesInitializer.LABEL_piecewise_template_size);
			for (int i = 2; i <= maxSize; i++) {
				templates.add(new PiecewiseTemplate(i));
			}
		}
		if (store.getBoolean(PreferencesInitializer.LABEL_enable_lex_template)) {
			int maxSize = store.getInt(PreferencesInitializer.LABEL_lex_template_size);
			for (int i = 2; i <= maxSize; i++) {
				templates.add(new LexicographicTemplate(i));
			}
		}
		return templates.toArray(new RankingFunctionTemplate[0]);
	}
	
	

	
	
	/**
	 * Build a list of templates. Add all templates with exactly the given size.
	 * @param preferences
	 * @return the templates specified in the preferences
	 */
	private RankingFunctionTemplate[] getTemplatesExactly() {
		UltimatePreferenceStore store =
				new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		List<RankingFunctionTemplate> templates =
				new ArrayList<RankingFunctionTemplate>();
		
		if (store.getBoolean(PreferencesInitializer.LABEL_enable_affine_template)) {
			templates.add(new AffineTemplate());
		}
		if (store.getBoolean(PreferencesInitializer.LABEL_enable_nested_template)) {
			templates.add(new NestedTemplate(store.getInt(
					PreferencesInitializer.LABEL_nested_template_size)));
		}
		if (store.getBoolean(PreferencesInitializer.LABEL_enable_multiphase_template)) {
			templates.add(new MultiphaseTemplate(store.getInt(
					PreferencesInitializer.LABEL_multiphase_template_size)));
		}
		if (store.getBoolean(PreferencesInitializer.LABEL_enable_piecewise_template)) {
			templates.add(new PiecewiseTemplate(store.getInt(
					PreferencesInitializer.LABEL_piecewise_template_size)));
		}
		if (store.getBoolean(PreferencesInitializer.LABEL_enable_lex_template)) {
			templates.add(new LexicographicTemplate(store.getInt(
					PreferencesInitializer.LABEL_lex_template_size)));
		}
		return templates.toArray(new RankingFunctionTemplate[0]);
	}
	
	private boolean isTerminationArgumentCorrect(TerminationArgument arg) {
		SmtManager smtManager = new SmtManager(
				m_RootAnnot.getBoogie2SMT(),
				m_RootAnnot.getModGlobVarManager());
		BinaryStatePredicateManager bspm = new BinaryStatePredicateManager(smtManager);
		bspm.computePredicates(false, arg);

		NestedWord<CodeBlock> stemNw = 
				new NestedWord<CodeBlock>(m_Stem, NestedWord.INTERNAL_POSITION);
		NestedWord<CodeBlock> loopNw = new 
				NestedWord<CodeBlock>(m_Loop, NestedWord.INTERNAL_POSITION);
		
		// check supporting invariants
		boolean siCorrect = true;
			for (SupportingInvariant si : 
					bspm.getTerminationArgument().getSupportingInvariants()) {
				siCorrect &= bspm.checkSupportingInvariant(si, stemNw, loopNw, 
						m_RootAnnot.getModGlobVarManager());
			}
		
		// check ranking function
		boolean rfCorrect = bspm.checkRankDecrease(loopNw, 
				m_RootAnnot.getModGlobVarManager());
		if (siCorrect && rfCorrect) {
			s_Logger.info("Termination argument has been successfully verified.");
		}
		return siCorrect && rfCorrect;
	}
	
	/**
	 * @return the current translator sequence for building results
	 */
	private List<ITranslator<?, ?, ?, ?>> getTranslatorSequence() {
		// getTranslatorSequence() is marked deprecated, but an alternative
		// has yet to arise
		List<ITranslator<?, ?, ?, ?>> translator_sequence =
			UltimateServices.getInstance().getTranslatorSequence();
		return translator_sequence;
	}
	
	/**
	 * Report a termination argument back to Ultimate's toolchain.
	 * @param arg the termination argument
	 */
	private void reportTerminationResult(TerminationArgument arg) {
		RankingFunction rf = arg.getRankingFunction();
		Collection<SupportingInvariant> si_list = arg.getSupportingInvariants();
		
		Script script = m_RootAnnot.getScript();
		Term2Expression smt2boogie = m_RootAnnot.getBoogie2SMT().getTerm2Expression();
		
		Expression[] supporting_invariants = new Expression[si_list.size()];
		int i = 0;
		for (SupportingInvariant si : si_list) {
			supporting_invariants[i] = si.asExpression(script, smt2boogie);
			++i;
		}
		
		TerminationArgumentResult<RcfgElement> result = 
				new TerminationArgumentResult<RcfgElement>(
					m_Honda,
					Activator.s_PLUGIN_NAME,
					rf.asLexExpression(script, smt2boogie),
					rf.getName(),
					supporting_invariants,
					getTranslatorSequence()
				);
		reportResult(result);
	}
	
	/**
	 * Report a nontermination argument back to Ultimate's toolchain
	 * @param arg
	 */
	private void reportNonTerminationResult(NonTerminationArgument arg) {
		// TODO: translate BoogieVars to Expressions?
		// m_RootAnnot.getBoogie2Smt().translate(term)
		
		NonTerminationArgumentResult<RcfgElement> result = 
				new NonTerminationArgumentResult<RcfgElement>(
					m_Honda,
					Activator.s_PLUGIN_NAME,
					NonTerminationArgument.rank2Boogie(arg.getStateInit()),
					NonTerminationArgument.rank2Boogie(arg.getStateHonda()),
					NonTerminationArgument.rank2Boogie(arg.getRay()),
					arg.getLambda(),
					getTranslatorSequence()
				);
		reportResult(result);
	}
	
	/**
	 * Report that no result has been found to Ultimate's toolchain
	 * @param preferences the current preferences
	 */
	private void reportNoResult(RankingFunctionTemplate[] templates) {
		NoResult<RcfgElement> result = new NoResult<RcfgElement>(
				m_Honda,
				Activator.s_PLUGIN_NAME,
				getTranslatorSequence()
		);
		result.setShortDescription("LassoRanker could not prove termination");
		StringBuilder sb = new StringBuilder();
		sb.append("LassoRanker could not prove termination " +
				"or nontermination of the given linear lasso program.\n");
		sb.append("Templates:");
		for (RankingFunctionTemplate template : templates) {
			sb.append(" ");
			sb.append(template.getClass().getSimpleName());
		}
		result.setLongDescription(sb.toString());
		s_Logger.info(sb.toString());
		reportResult(result);
	}
	
	/**
	 * Report that there was a timeout.
	 * TODO: which templates already failed, where did the timeout occur.
	 */
	private void reportTimeoutResult(RankingFunctionTemplate[] templates, 
			RankingFunctionTemplate templateWhereTimeoutOccurred) {
		StringBuilder sb = new StringBuilder();
		sb.append("LassoRanker could not prove termination " +
				"or nontermination of the given linear lasso program.\n");
		sb.append("Templates:");
		for (RankingFunctionTemplate template : templates) {
			sb.append(" ");
			sb.append(template.getClass().getSimpleName());
		}
		TimeoutResultAtElement<RcfgElement> result = new TimeoutResultAtElement<RcfgElement>(
				m_Honda,
				Activator.s_PLUGIN_NAME,
				getTranslatorSequence(),
				sb.toString()
		);
		s_Logger.info(sb.toString());
		reportResult(result);
	}
	
	
	/**
	 * Report that unsupported syntax was discovered
	 * @param position the program point
	 * @param message an error message explaining the problem
	 */
	private void reportUnuspportedSyntax(RcfgElement position, String message) {
		s_Logger.error(message);
		UnsupportedSyntaxResult<RcfgElement> result = 
				new UnsupportedSyntaxResult<RcfgElement>(
				position,
				Activator.s_PLUGIN_NAME,
				getTranslatorSequence(),message);
		reportResult(result);
	}
	
	/**
	 * Report a result back to the Ultimate toolchain
	 * @param result the result
	 */
	private void reportResult(IResult result) {
		UltimateServices.getInstance().reportResult(
				Activator.s_PLUGIN_ID,
				result
		);
	}
	
	
	private void checkRCFGBuilderSettings() {
		String rcfgBuilderPluginId = de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator.PLUGIN_ID;
		UltimatePreferenceStore store =
				new UltimatePreferenceStore(rcfgBuilderPluginId);
		String removeGotoLabel = de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceInitializer.LABEL_RemoveGotoEdges;
		boolean removeGoto = store.getBoolean(removeGotoLabel);
		String codeBlockSizeLabel = de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceInitializer.LABEL_CodeBlockSize;
		Class<CodeBlockSize> cbsClass = de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceInitializer.CodeBlockSize.class;
		CodeBlockSize codeBlockSize = store.getEnum(codeBlockSizeLabel, cbsClass);
		if (codeBlockSize != CodeBlockSize.LoopFreeBlock) {
			throw new UnsupportedOperationException("Unsupported input: Use the large block encoding of the RCFGBuilder");
		}
		if (!removeGoto) {
			throw new UnsupportedOperationException("Unsupported input: Let RCFGBuilder remove goto edges");
		}
		
				
				
	}

}
