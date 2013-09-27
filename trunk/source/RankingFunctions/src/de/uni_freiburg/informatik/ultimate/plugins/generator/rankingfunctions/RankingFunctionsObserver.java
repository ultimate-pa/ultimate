package de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions;

import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogieStatementPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.functions.LinearRankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.functions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.templates.LinearTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.templates.MultiPhaseTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.templates.RankingTemplate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceValues.Solver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.NoResult;
import de.uni_freiburg.informatik.ultimate.result.RankingFunctionResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult.SyntaxErrorType;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor;


/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class RankingFunctionsObserver implements IUnmanagedObserver {

	private static Logger s_Logger =
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	/**
	 * Collection of ranking templates to be instantiated
	 */
	public Collection<Class<? extends RankingTemplate>> m_templates;
	
	private ProgramPoint honda;
	
	public RankingFunctionsObserver() {
		m_templates = new ArrayList<Class<? extends RankingTemplate>>();
		
		// Fill the templates list with all relevant template classes
		if (Preferences.use_linear_template) {
			m_templates.add(LinearTemplate.class);
		}
		if (Preferences.use_multiphase_template) {
			m_templates.add(MultiPhaseTemplate.class);
		}
	}
	
	/**
	 * Create a new SMT solver instance.
	 * Accesses the RCFGBuilder preferences for solver settings.
	 * 
	 * @param nonlinear Is non-linear arithmetic required?
	 */
	Script new_Script(boolean nonlinear) {
		// This code is essentially copied from 
		// de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CfgBuilder
		// since there is no obvious way to implement it as shared code.
		
		TAPreferences taPref = new TAPreferences();
		Logger solverLogger = Logger.getLogger("interpolLogger");
		Script script;
		
		if (taPref.solver() == Solver.SMTInterpol) {
			script = new SMTInterpol(solverLogger,false);
		} else if (taPref.solver() == Solver.Z3) {
			script = new Scriptor("z3 -smt2 -in", solverLogger);
		} else {
			throw new AssertionError();
		}
		
		if (taPref.dumpScript()) {
			String dumpFileName = taPref.dumpPath();
			String fileSep = System.getProperty("file.separator");
			dumpFileName += (dumpFileName.endsWith(fileSep) ? "" : fileSep);
			dumpFileName = dumpFileName + "rankingFunctions.smt2";
			// FIXME: add file name
			try {
				script = new LoggingScript(script, dumpFileName, true);
			} catch (FileNotFoundException e) {
				throw new AssertionError(e);
			}
		}
		
//		script.setOption(":produce-unsat-cores", true);
		script.setOption(":produce-models", true);
		if (taPref.solver() == Solver.SMTInterpol) {
			script.setLogic(nonlinear ? "QF_NRA" : "QF_LRA");
		} else if (taPref.solver() == Solver.Z3) {
			script.setLogic(nonlinear ? "QF_NRA" : "QF_LRA");
		} else {
			throw new AssertionError();
		}
		return script;
	}
	
	@Override
	public boolean process(IElement root) {
		RootNode rootNode = (RootNode) root;
		List<RCFGNode> rootSucc = rootNode.getOutgoingNodes();
		RCFGNode firstNode;
		boolean cacslTranslated = false;
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
			} else {
				cacslTranslated = true;
			}
		}
//		assert(rootSucc.size() == 1);
		List<RCFGEdge> stemEdges = firstNode.getOutgoingEdges();
//		assert(stemEdges.size() == 1);
		CodeBlock stemEdge = (CodeBlock) stemEdges.get(0);
		honda = (ProgramPoint) stemEdge.getTarget();
		CodeBlock loopEdge = null;
		if (honda.getOutgoingEdges().size() == 2) {
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
			
			Script old_script = rootNode.getRootAnnot().getScript();
			Script script;
			if (Preferences.use_new_script) {
				script = new_Script(Preferences.not_nondecreasing);
			} else {
				script = old_script;
				script.push(1);
			}
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
			for (Class<? extends RankingTemplate> template : m_templates) {
				try {
					// Call the synthesizer
					RankingFunctionsSynthesizer synthesizer =
							new RankingFunctionsSynthesizer(old_script, script,
									stem, loop);

					if (synthesizer.synthesize(template)) {
						RankingFunction rf = synthesizer.getRankingFunction();
						assert(rf != null);
						Collection<SupportingInvariant> si_list =
								synthesizer.getSupportingInvariants();
						assert(si_list != null);

						StringBuilder longMessage = new StringBuilder();
						if (rf instanceof LinearRankingFunction) {
							LinearRankingFunction linRf = (LinearRankingFunction) rf;
							Expression rfExp = linRf.asExpression(old_script, rootNode.getRootAnnot().getBoogie2Smt());
							String rfString = backtranslateExprWorkaround(rfExp);
							String siString = "";
							if (si_list.size() <= 2) {
								SupportingInvariant si = si_list.iterator().next();
								Expression siExp = si.asExpression(old_script, rootNode.getRootAnnot().getBoogie2Smt());
								siString = backtranslateExprWorkaround(siExp);
							} else {
								for (SupportingInvariant si : si_list) {
									Expression siExp = si.asExpression(old_script, rootNode.getRootAnnot().getBoogie2Smt());
									siString += backtranslateExprWorkaround(siExp) + ", ";
								}
//								throw new AssertionError("The linear template should not have more than two supporting invariants.");
							}
							longMessage.append("Found linear ranking function ");
							longMessage.append(rfString);
							longMessage.append(" with linear supporting invariant ");
							longMessage.append(siString);
						} else {
							longMessage.append("A ranking function has been found:");
							longMessage.append("\n" + rf);
							boolean first = true;
							for (SupportingInvariant si : si_list) {
								if (!si.isTrivial()) {
									if (first) {
										longMessage.append("\n" + "Provided with the supporting "
												+ "invariants:");
										first = false;
									}
									longMessage.append("\n" + si);
								}
							}
						}
						s_Logger.info(longMessage);
						String shortMessage;
						if (rf instanceof LinearRankingFunction) {
							shortMessage = "Found linear ranking function with supporting invariant";
						} else {
							shortMessage = rf.getClass().getName();
						}
						RankingFunctionResult<RcfgElement> rankRes = 
								new RankingFunctionResult<RcfgElement>(
								honda,
								Activator.s_PLUGIN_NAME,
								UltimateServices.getInstance().getTranslatorSequence(),
								honda.getAstNode().getLocation().getOrigin(),
								shortMessage,
								longMessage.toString());
						reportResult(rankRes);
						return false;
					}
					if (template.equals(LinearTemplate.class)) {
						String shortMessage = "No ranking function found";
						String longMessage = "No linear ranking function with linear supporting invariant found.";
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
				} catch (InstantiationException e) {
					s_Logger.error("Failed to instantiate the template.");
				} catch (TermIsNotAffineException e) {
					s_Logger.error(e);
				} catch (SMTLIBException e) {
					s_Logger.error(e);
				} catch (Exception e) {
					s_Logger.error(e);
				}
			}
			s_Logger.info("There are no more templates to try. I give up. :/");
			
			if (!Preferences.use_new_script) {
				script.pop(1);
			}
		} else {
			reportUnuspportedSyntax(honda);
		}
		return false;
	}
	
	private void reportResult(IResult res) {
		UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID, res);
	}

	@Override
	public void finish() {
		// TODO Auto-generated method stub
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void init() {
		// TODO Auto-generated method stub
	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
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
}
