package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.*;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Smt2Boogie;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preferences.PreferencesInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preferences.Preferences;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates.*;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.NoResult;
import de.uni_freiburg.informatik.ultimate.result.NonTerminationArgumentResult;
import de.uni_freiburg.informatik.ultimate.result.TerminationArgumentResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult.SyntaxErrorType;


/**
 * Observer for LassoRanker
 * 
 * Extracts the lasso program's stem and loop transition from the RCFG builder's
 * transition graph. This is then passed to the LassoRankerTerminationAnalysis
 * class, which serves as an interface to LassoRanker's termination and
 * non-termination analysis methods.
 * 
 * Termination and non-termination arguments are synthesizer via constraint
 * solving. The generated constraints are non-linear algebraic constraints.
 * We use an external SMT solver to solve these constraints.
 * 
 * @see LassoRankerTerminationAnalysis
 * @author Matthias Heizmann, Jan Leike
 */
public class LassoRankerObserver implements IUnmanagedObserver {
	private static Logger s_Logger =
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	private static final String s_lasso_error =
			"This is not a lasso program (a lasso program is a program " +
			"consisting of a stem and a loop transition)";
	
	private ProgramPoint m_Honda;
	private RootNode m_RootNode;
	private TransFormula m_Stem;
	private TransFormula m_Loop;
	
	/**
	 * Build a list of templates
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
		if (store.getBoolean(PreferencesInitializer.LABEL_enable_multiphase_template)) {
			templates.add(new MultiphaseTemplate(store.getInt(
					PreferencesInitializer.LABEL_multiphase_template_size)));
		}
		if (store.getBoolean(PreferencesInitializer.LABEL_enable_piecewise_template)) {
			s_Logger.error("Piecewise Template is currently broken. :'("); // FIXME
			templates.add(new PiecewiseTemplate(store.getInt(
					PreferencesInitializer.LABEL_piecewise_template_size)));
		}
		if (store.getBoolean(PreferencesInitializer.LABEL_enable_lex_template)) {
			templates.add(new LexicographicTemplate(store.getInt(
					PreferencesInitializer.LABEL_lex_template_size)));
		}
		return templates.toArray(new RankingFunctionTemplate[0]);
	}
	
	/**
	 * Check if List contains exactly two nodes and one node is from the 
	 * ULTIMATE.init procedure. If this is the case, return the other node.
	 * Otherwise return null.
	 */
	private RCFGNode checkIfTwoNodesAndOneFromInit(List<RCFGNode> rootSucc) {
		if (rootSucc.size() != 2) {
			return null;
		}
		if (isProgramPointOfInitProcedure((ProgramPoint) rootSucc.get(0))) {
			return rootSucc.get(1);
		}
		if (isProgramPointOfInitProcedure((ProgramPoint) rootSucc.get(1))) {
			return rootSucc.get(0);
		}
		return null;
	}
	
	private boolean isProgramPointOfInitProcedure(ProgramPoint pp) {
		return pp.getProcedure().equals("ULTIMATE.init");
	}
	
	/**
	 * Extract a stem and loop transition from a lasso program provided as a
	 * CFG by the toolchain
	 * @return whether the extraction was successful
	 */
	private boolean extractLasso() {
		List<RCFGNode> rootSucc = m_RootNode.getOutgoingNodes();
		RCFGNode firstNode;
		if (rootSucc.size() == 1) {
			firstNode = rootSucc.get(0);
		} else {
			firstNode = checkIfTwoNodesAndOneFromInit(rootSucc);
			if (firstNode == null) {
				for (RCFGNode succ : rootSucc) {
					if (!isProgramPointOfInitProcedure((ProgramPoint) succ)) {
						reportUnuspportedSyntax((ProgramPoint) succ,
								s_lasso_error);
					}
				}
			}
		}
//		assert(rootSucc.size() == 1);
		List<RCFGEdge> stemEdges = firstNode.getOutgoingEdges();
//		assert(stemEdges.size() == 1);
		CodeBlock stemEdge = (CodeBlock) stemEdges.get(0);
		m_Honda = (ProgramPoint) stemEdge.getTarget();
		CodeBlock loopEdge = null;
		if (m_Honda.getOutgoingEdges().size() != 2) {
			reportUnuspportedSyntax(m_Honda, s_lasso_error);
			return false;
		}
		for (RCFGEdge hondaSucc : m_Honda.getOutgoingEdges()) {
			if (hondaSucc.getTarget() == m_Honda) {
				loopEdge = (CodeBlock) hondaSucc;
			} else {
				ProgramPoint interposition = (ProgramPoint) hondaSucc.getTarget();
				for (RCFGEdge interpositionSucc : interposition.getOutgoingEdges()) {
					if (interpositionSucc.getTarget() == m_Honda) {
						loopEdge = (CodeBlock) interpositionSucc;
					}					
				}
			}
		}
		if (loopEdge == null) {
			reportUnuspportedSyntax(m_Honda, s_lasso_error);
			return false;
		}
		
		Script script = m_RootNode.getRootAnnot().getScript();
		{
			m_Stem = stemEdge.getTransitionFormula();
			m_Loop = loopEdge.getTransitionFormula();
//			stem = stem.sequentialComposition(stem, loop, script);
			TermVariableRenamer tvr = new TermVariableRenamer(script);
			m_Stem = tvr.renameVars(m_Stem, "Stem");
			m_Loop = tvr.renameVars(m_Loop, "Loop");
		}
		return true;
	}
	
	@Override
	public boolean process(IElement root) {
		UltimatePreferenceStore store =
				new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		Preferences preferences = Preferences.getGuiPreferences();
		s_Logger.info("Preferences:\n" + preferences.show());
		
		assert(root instanceof RootNode);
		m_RootNode = (RootNode) root;
		
		if (!extractLasso()) {
			return false;
		}
		Script script = m_RootNode.getRootAnnot().getScript();
		
		// Do the termination analysis
		LassoRankerTerminationAnalysis tanalysis;
		try {
			tanalysis = new LassoRankerTerminationAnalysis(script, m_Stem,
					m_Loop, preferences);
		} catch (TermException e) {
			reportUnuspportedSyntax(m_Honda, e.getMessage());
			return false;
		}
		
		// Try to prove non-termination
		if (store.getBoolean(PreferencesInitializer.LABEL_check_for_nontermination)) {
			try {
				NonTerminationArgument arg = tanalysis.checkNonTermination();
				if (arg != null) {
					reportNonTerminationResult(arg);
					return false;
				}
			} catch (SMTLIBException e) {
				s_Logger.error(e);
			}
		}
		
		// Try all given templates
		RankingFunctionTemplate[] templates = getTemplates();
		for (RankingFunctionTemplate template : templates) {
			if (!UltimateServices.getInstance().continueProcessing()) {
				// Timeout or abort
				return false;
			}
			try {
				TerminationArgument arg = tanalysis.tryTemplate(template);
				if (arg != null) {
					reportTerminationResult(arg);
					return false;
				}
			} catch (TermException e) {
				s_Logger.error(e);
			} catch (SMTLIBException e) {
				s_Logger.error(e);
			}
		}
		tanalysis.cleanUp();
		reportNoResult(templates);
		return false;
	}
	
	/**
	 * @return the current translator sequence for building results
	 */
	private List<ITranslator<?, ?, ?, ?>> getTranslatorSequence() {
		// getTranslatorSequence() is marked deprecated, but an alternative
		// has yet to arise
		@SuppressWarnings("deprecation")
		List<ITranslator<?, ?, ?, ?>> translator_sequence =
			UltimateServices.getInstance().getTranslatorSequence();
		return translator_sequence;
	}
	
	/**
	 * @return the current location for building results
	 */
	private ILocation getLocation() {
		// Deprecated method without replacement
		@SuppressWarnings("deprecation")
		ILocation location = m_Honda.getAstNode().getLocation().getOrigin();
		return location;
	}
	
	/**
	 * Report a termination argument back to Ultimate's toolchain.
	 * @param arg the termination argument
	 */
	private void reportTerminationResult(TerminationArgument arg) {
		RankingFunction rf = arg.getRankingFunction();
		Collection<SupportingInvariant> si_list = arg.getSupportingInvariants();
		
		Script script = m_RootNode.getRootAnnot().getScript();
		Smt2Boogie smt2boogie = m_RootNode.getRootAnnot().getBoogie2Smt();
		
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
					rf.getClass().getName(),
					supporting_invariants,
					getTranslatorSequence(),
					getLocation()
				);
		reportResult(result);
	}
	
	/**
	 * Report a nontermination argument back to Ultimate's toolchain
	 * @param arg
	 */
	private void reportNonTerminationResult(NonTerminationArgument arg) {
		// TODO: translate BoogieVars to Expressions?
		// m_RootNode.getRootAnnot().getBoogie2Smt().translate(term)
		NonTerminationArgumentResult<RcfgElement> result = 
				new NonTerminationArgumentResult<RcfgElement>(
					m_Honda,
					Activator.s_PLUGIN_NAME,
					arg.getStateInit(),
					arg.getStateHonda(),
					arg.getRay(),
					arg.getLambda(),
					getTranslatorSequence(),
					getLocation()
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
				getTranslatorSequence(),
				getLocation()
		);
		result.setShortDescription("LassoRanker could not prove termination");
		StringBuilder sb = new StringBuilder();
		sb.append("LassoRanker could not prove termination " +
				"or nontermination of the given linear lasso program.\n");
		sb.append("Templates: ");
		for (RankingFunctionTemplate template : templates) {
			sb.append(template.getClass().getName());
		}
		result.setLongDescription(sb.toString());
		reportResult(result);
	}
	
	/**
	 * Report that unsupported syntax was discovered
	 * @param position the program point
	 * @param message an error message explaining the problem
	 */
	private void reportUnuspportedSyntax(ProgramPoint position, String message) {
		s_Logger.error(message);
		
		SyntaxErrorResult<RcfgElement> result = 
				new SyntaxErrorResult<RcfgElement>(
				position,
				Activator.s_PLUGIN_NAME,
				getTranslatorSequence(),
				getLocation(),
				SyntaxErrorType.UnsupportedSyntax);
		result.setLongDescription(message);
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
	
	/**
	 * @return the root of the CFG.
	 */
	public INode getRoot(){
		return null;
	}
	
	@Override
	public void init() {
//		Ordinal.testcases();
	}

	@Override
	public void finish() {
		// nothing to do
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null; // not required
	}

	@Override
	public boolean performedChanges() {
		return false;
	}
}