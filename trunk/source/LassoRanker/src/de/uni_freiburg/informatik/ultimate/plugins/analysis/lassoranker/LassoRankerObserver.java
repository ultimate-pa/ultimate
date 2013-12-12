package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.*;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogieStatementPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Smt2Boogie;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preferences.Preferences;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.LinearRankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.Ordinal;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates.AffineTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates.LexicographicTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates.MultiphaseTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates.PiecewiseTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates.RankingFunctionTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.NoResult;
import de.uni_freiburg.informatik.ultimate.result.RankingFunctionResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult.SyntaxErrorType;


/**
 * Observer for LassoRanker.
 * 
 * Extract the lasso program's stem and loop transition from the RCFG builder's
 * transition graph.  This is then passed to the Synthesizer, which tries to
 * find a ranking function for this lasso program.
 * 
 * Ranking function synthesis is done via constraint solving.  The generated
 * constraints are non-linear algebraic constraints.
 * @see SMTSolver SMTSolver for access to the smt solver script
 * 
 * @author Matthias Heizmann, Jan Leike
 */
public class LassoRankerObserver implements IUnmanagedObserver {
	private static Logger s_Logger =
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	private ProgramPoint honda;
	
	public LassoRankerObserver() {
		
	}
	
	/**
	 * Build a list of templates
	 * @param preferences
	 * @return the templates specified in the preferences
	 */
	protected Collection<RankingFunctionTemplate> getTemplates(
			Preferences preferences) {
		Collection<RankingFunctionTemplate> templates =
				new ArrayList<RankingFunctionTemplate>();
		
		if (preferences.use_affine_template) {
			templates.add(new AffineTemplate());
		}
		if (preferences.use_multiphase_template) {
			templates.add(new MultiphaseTemplate(preferences.multiphase_template_size));
		}
		if (preferences.use_piecewise_template) {
			s_Logger.error("Piecewise Template is currently broken. :'("); // FIXME
			templates.add(new PiecewiseTemplate(preferences.piecewise_template_size));
		}
		if (preferences.use_lex_template) {
			templates.add(new LexicographicTemplate(preferences.lex_template_size));
		}
		return templates;
	}
	
	/**
	 * Create an informative message about the result of the synthesis process
	 * @param synthesizer the synthesizer after calling .synthesize()
	 * @return long descriptive message
	 */
	private String resultMessage(Synthesizer synthesizer, Script script, Smt2Boogie smt2boogie) {
		RankingFunction rf = synthesizer.getRankingFunction();
		Collection<SupportingInvariant> si_list =
				synthesizer.getSupportingInvariants();
		if (rf == null) {
			return "No ranking function found.";
		}
		assert(si_list != null);
		
		// Check if a supporting invariant was needed
		boolean has_si = false;
		for (SupportingInvariant si : si_list) {
			if (!si.isTrue()) {
				has_si = true;
				break;
			}
		}
		
		StringBuilder sb = new StringBuilder();
		if (rf instanceof LinearRankingFunction) {
			LinearRankingFunction linRf = (LinearRankingFunction) rf;
			Expression rfExp = linRf.asExpression(script, smt2boogie);
			String rfString = backtranslateExprWorkaround(rfExp);
			String siString = "";
			for (SupportingInvariant si : si_list) {
				if (!si.isTrue()) {
					Expression siExp = si.asExpression(script, smt2boogie);
					siString += backtranslateExprWorkaround(siExp) + ", ";
				}
			}
			sb.append("Found linear ranking function ");
			sb.append(rfString);
			if (has_si) {
				sb.append(" with linear supporting invariants ");
				sb.append(siString);
			}
			sb.append(".");
		} else {
			sb.append("A ranking function has been found:\n");
			sb.append(rf);
			if (has_si) {
				sb.append("\nProvided with the supporting invariants:");
				for (SupportingInvariant si : si_list) {
					if (!si.isTrue()) {
						sb.append("\n");
						sb.append(si);
					}
				}
			}
		}
		return sb.toString();
	}
	
	@Override
	public boolean process(IElement root) {
		// TODO: insert preferences here
		Preferences preferences = new Preferences();
		s_Logger.info("Preferences:\n" + preferences.show());
		
		RootNode rootNode = (RootNode) root;
		List<RCFGNode> rootSucc = rootNode.getOutgoingNodes();
		RCFGNode firstNode;
		if (rootSucc.size() == 1) {
			firstNode = rootSucc.get(0);
		} else {
			firstNode = checkIfTwoNodesAndOneFromInit(rootSucc);
			if (firstNode == null) {
				for (RCFGNode succ : rootSucc) {
					if (!isProgramPointOfInitProcedure((ProgramPoint) succ)) {
						reportUnuspportedSyntax((ProgramPoint) succ);
					}
				}
			}
		}
//		assert(rootSucc.size() == 1);
		List<RCFGEdge> stemEdges = firstNode.getOutgoingEdges();
//		assert(stemEdges.size() == 1);
		CodeBlock stemEdge = (CodeBlock) stemEdges.get(0);
		honda = (ProgramPoint) stemEdge.getTarget();
		CodeBlock loopEdge = null;
		if (honda.getOutgoingEdges().size() != 2) {
			reportUnuspportedSyntax(honda);
			return false;
		}
		for (RCFGEdge hondaSucc : honda.getOutgoingEdges()) {
			if (hondaSucc.getTarget() == honda) {
				loopEdge = (CodeBlock) hondaSucc;
			} else {
				ProgramPoint interposition = (ProgramPoint) hondaSucc.getTarget();
				for (RCFGEdge interpositionSucc : interposition.getOutgoingEdges()) {
					if (interpositionSucc.getTarget() == honda) {
						loopEdge = (CodeBlock) interpositionSucc;
					}					
				}
			}
		}
		if (loopEdge == null) {
			reportUnuspportedSyntax(honda);
			return false;
		}
		
		Script script = rootNode.getRootAnnot().getScript();
		TransFormula stem;
		TransFormula loop;
		{
			stem = stemEdge.getTransitionFormula();
			loop = loopEdge.getTransitionFormula();
			//			stem = stem.sequentialComposition(stem, loop, script);
			TermVariableRenamer tvr = new TermVariableRenamer(script);
			stem = tvr.renameVars(stem, "Stem");
			loop = tvr.renameVars(loop, "Loop");
		}
		
		// Try a number of possible templates
		for (RankingFunctionTemplate template : getTemplates(preferences)) {
			try {
				// Call the synthesizer
				Synthesizer synthesizer =
						new Synthesizer(script, stem, loop, preferences);
				
				if (synthesizer.synthesize(template)) {
					RankingFunction rf = synthesizer.getRankingFunction();
					Collection<SupportingInvariant> si_list =
							synthesizer.getSupportingInvariants();
					assert(rf != null);
					assert(si_list != null);
					
					String longMessage = resultMessage(synthesizer, script,
							rootNode.getRootAnnot().getBoogie2Smt());
					s_Logger.info(longMessage);
					
					@SuppressWarnings("deprecation")
					RankingFunctionResult<RcfgElement> rankRes = 
							new RankingFunctionResult<RcfgElement>(
							honda,
							Activator.s_PLUGIN_NAME,
							UltimateServices.getInstance().getTranslatorSequence(),
							honda.getAstNode().getLocation().getOrigin(),
							rf.getClass().getName(),
							longMessage.toString());
					reportResult(rankRes);
					return false;
				}
				if (template instanceof AffineTemplate) {
					String shortMessage = "No ranking function found";
					String longMessage = "No linear ranking function with linear supporting invariant found.";
					
					@SuppressWarnings("deprecation")
					NoResult<RcfgElement> rankRes = 
							new NoResult<RcfgElement>(
							honda,
							Activator.s_PLUGIN_NAME,
							UltimateServices.getInstance().getTranslatorSequence(),
							honda.getAstNode().getLocation().getOrigin());
					rankRes.setShortDescription(shortMessage);
					rankRes.setLongDescription(longMessage.toString());
					reportResult(rankRes);
				}
				s_Logger.info("No ranking function has been found " +
						"with this template.");
			} catch (TermException e) {
				s_Logger.error(e);
			} catch (SMTLIBException e) {
				s_Logger.error(e);
			} catch (Exception e) {
				s_Logger.error(e);
			}
		}
		s_Logger.info("There are no more templates to try. I give up. :/");
		return false;
	}
	
	private void reportResult(IResult res) {
		UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID, res);
	}
	
	/**
	 * @return the root of the CFG.
	 */
	public INode getRoot(){
		return null;
	}
	
	/**
	 * Check if List contains exactly two nodes and one node is from the 
	 * ULTIMATE.init procedure. If this is the case, return the other node.
	 * Otherwise return null.
	 */
	private RCFGNode checkIfTwoNodesAndOneFromInit (List<RCFGNode> rootSucc) {
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
	
	private void reportUnuspportedSyntax(ProgramPoint position) {
		String message = "This is not a lasso program (a lasso program is a single procedure with a single while loop and without branching, neither in the stem nor in the body of the while loop)";
		s_Logger.error(message);
		
		@SuppressWarnings("deprecation") // Daniels ModelContainer
		SyntaxErrorResult<RcfgElement> unsupp = 
				new SyntaxErrorResult<RcfgElement>(
				position,
				Activator.s_PLUGIN_NAME,
				UltimateServices.getInstance().getTranslatorSequence(),
				position.getAstNode().getLocation().getOrigin(),
				SyntaxErrorType.UnsupportedSyntax);
		unsupp.setLongDescription(message);
		reportResult(unsupp);
	}
	
	public static String backtranslateExprWorkaround(Expression expr) {
		@SuppressWarnings("deprecation") // Daniels ModelContainer
		ITranslator<?, ?, Expression, ?> iback = 
				(ITranslator<?, ?, Expression, ?>) UltimateServices.getInstance().getTranslatorSequence().get(0);
		Object backExpr = iback.translateExpression(expr);
		String ppExpr;
		if (backExpr instanceof String) {
			ppExpr = (String) backExpr;
//			ppExpr += "  Internal BoogieExpression: ";
//			ppExpr += BoogieStatementPrettyPrinter.print((Expression) expr);
		} else if (backExpr instanceof Expression) {
			ppExpr = BoogieStatementPrettyPrinter.print((Expression) backExpr);
		} else {
			throw new AssertionError();
		}
		return ppExpr;
	}

	@Override
	public void init() {
		Ordinal.testcases();
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