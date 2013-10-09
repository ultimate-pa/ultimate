package de.uni_freiburg.informatik.ultimate.plugins.generator.impulse;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.errortrace.ErrorTrace;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.GraphWriter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceValues.Solver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;

import org.apache.log4j.Logger;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class ImpulseObserver implements IUnmanagedObserver {

	public enum Result { CORRECT, TIMEOUT , MAXEDITERATIONS , UNKNOWN , INCORRECT }

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	private RootNode m_originalRoot;
	private SmtManager m_smtManager;
	private TAPreferences m_taPrefs;
	private ImpRootNode m_graphRoot;

	private IPredicate m_truePredicate;
	private IPredicate m_falsePredicate;
	private ProgramPoint m_pELProgramPoint;

	private HashMap<AnnotatedProgramPoint, AnnotatedProgramPoint> m_nodeToCopy;
	private HashMap<AnnotatedProgramPoint, AnnotatedProgramPoint> m_nodeToCopyCurrent;
	private AnnotatedProgramPoint m_currentProcRoot;

	private HashMap<AnnotatedProgramPoint, ArrayList<AnnotatedProgramPoint>> m_callPredToReturnPreds;

	private HashMap<ProgramPoint, ArrayList<AnnotatedProgramPoint>> m_programPointToItsAnnotatedPPs;
	private HashMap<ProgramPoint, ArrayList<AnnotatedProgramPoint>> m_programPointToItsAnnotatedPPsInit;

	GraphWriter m_gw;
	int m_gwCounter = 0;

	int m_pathChecks = 0;
	private ErrorTrace m_errorTrace;

	@Override
	public boolean process(IElement root) {
		m_originalRoot = (RootNode) root;
		RootAnnot rootAnnot = m_originalRoot.getRootAnnot();
		m_taPrefs = rootAnnot.getTaPrefs();
		m_smtManager = new SmtManager(rootAnnot.getBoogie2SMT(), 
				Solver.SMTInterpol, rootAnnot.getGlobalVars(), null, false, "");

		m_truePredicate = m_smtManager.newTruePredicate();
		m_falsePredicate = m_smtManager.newFalsePredicate();
		m_pELProgramPoint = new ProgramPoint("PEL", "all", true, null, null, m_smtManager.getScript());

				m_gw  = new GraphWriter("C:/data/dumps",
//		m_gw  = new GraphWriter("",
				true, true, true, true, m_smtManager.getScript());

		RCFG2AnnotatedRCFG r2ar = new RCFG2AnnotatedRCFG(m_smtManager);
		m_graphRoot = r2ar.convert(m_originalRoot);
//		m_programPointToItsAnnotatedPPsInit = new HashMap<ProgramPoint, ArrayList<AnnotatedProgramPoint>>();
//		for (Entry<ProgramPoint, AnnotatedProgramPoint> en : r2ar.getOldPpTonew().entrySet()) {
//			ArrayList<AnnotatedProgramPoint> apps = new ArrayList<AnnotatedProgramPoint>();
//			apps.add(en.getValue());
//			m_programPointToItsAnnotatedPPsInit.put(en.getKey(), apps);
//		}
//		m_callPredToReturnPreds = ((ImpRootAnnot) m_graphRoot.getRootAnnot()).getCallPredToReturnPreds();
//
//		Result overallResult = null;
//
//		for (AnnotatedProgramPoint procRoot : m_graphRoot.getOutgoingNodes()) {
//			Result procResult = processProcedure(procRoot);
//
//			if (overallResult == null || 
//					(overallResult == Result.CORRECT && procResult != Result.CORRECT))
//				overallResult = procResult;
//		}
//
//		s_Logger.info("-----------------");
//		s_Logger.info(overallResult);
//		s_Logger.info("-----------------");
//
//		s_Logger.info("PC#: " + m_smtManager.getInterpolQueries());
//		s_Logger.info("TIME#: " + m_smtManager.getInterpolQuriesTime());
//		s_Logger.info("ManipulationTIME#: " + m_smtManager.getTraceCheckTime());
//		s_Logger.info("EC#: " + m_smtManager.getNontrivialSatQueries());
//		s_Logger.info("TIME#: " + m_smtManager.getSatQuriesTime());
//		s_Logger.info("ManipulationTIME#: "	+ m_smtManager.getCodeBlockCheckTime());
//
//		if (overallResult == Result.CORRECT) {
//			PositiveResult<CodeBlock> result = new PositiveResult<CodeBlock>(
//					null,
//					Activator.s_PLUGIN_NAME,
//					UltimateServices.getInstance().getTranslatorSequence(),
//					this.m_graphRoot.getPayload().getLocation());
//			result.setShortDescription("Program is safe!");
//			reportResult(result);
//		} else if (overallResult == Result.INCORRECT) {
//			this.reportResult(new CounterExampleResult<CodeBlock>(null,
//					Activator.s_PLUGIN_NAME,
//					UltimateServices.getInstance().getTranslatorSequence(),
//					null, null));//m_errorTrace.getCounterExampleResult());
//		} else {
//			this.reportResult(new UnprovableResult<CodeBlock>(null,
//					Activator.s_PLUGIN_NAME,
//					UltimateServices.getInstance().getTranslatorSequence(),
//					null));
//		}

		return false;
	}

	private Result processProcedure(AnnotatedProgramPoint procRoot) {
		EmptinessCheck emptinessCheck = new EmptinessCheck();

		m_programPointToItsAnnotatedPPs = 
				(HashMap<ProgramPoint, ArrayList<AnnotatedProgramPoint>>) m_programPointToItsAnnotatedPPsInit.clone();

		m_nodeToCopy = new HashMap<AnnotatedProgramPoint, AnnotatedProgramPoint>();
		m_nodeToCopyCurrent = new HashMap<AnnotatedProgramPoint, AnnotatedProgramPoint>();
		m_currentProcRoot = procRoot;

		m_gw.writeGraphAsImage(m_currentProcRoot, "graph_" + (++m_gwCounter) + "_procproc");

		while (true) { //(m_pathChecks < 1) {
			s_Logger.info("did " + m_pathChecks + " iterations, starting new");
			Pair<AnnotatedProgramPoint[], NestedWord<CodeBlock>> errorNWP = 
					emptinessCheck.checkForEmptiness(procRoot);


			if (errorNWP == null) {
				m_gw.writeGraphAsImage(m_currentProcRoot, "graph_" + (++m_gwCounter) + "_provenCorrect");
				return Result.CORRECT;
			} else {
				s_Logger.debug("found an error path");
				boolean isPEL = errorNWP.getFirst()[errorNWP.getFirst().length - 1].
						isPseudoErrorLocation();
				AnnotatedProgramPoint pEL = isPEL ? errorNWP.getFirst()[errorNWP.getFirst().length - 1] : null;

				if (isPEL)
					s_Logger.debug("it is a Pseudo Error Location");

				m_gw.writeGraphAsImage(m_currentProcRoot,
						"graph_" + (++m_gwCounter) + "_ep", errorNWP.getFirst());

				TraceChecker traceChecker = new TraceChecker(m_truePredicate, 
						isPEL ? pEL.getPredicate() : m_falsePredicate, null,
								errorNWP.getSecond(), m_smtManager, 
						m_originalRoot.getRootAnnot().getModGlobVarManager());
				LBool isSafe = traceChecker.isCorrect();
				m_pathChecks++;

				if(isSafe == LBool.UNSAT) {
					PredicateUnifier pu = new PredicateUnifier(m_smtManager, m_truePredicate, m_falsePredicate);
					traceChecker.computeInterpolants(new TraceChecker.AllIntegers(), pu);
					IPredicate[] interpolants = traceChecker.getInterpolants();

					boolean writeDetailedGraphs = true;

					copyNodes(errorNWP, interpolants);
					if (writeDetailedGraphs)
						m_gw.writeGraphAsImage(m_currentProcRoot,
								"graph_" + (++m_gwCounter) + "_cp", m_nodeToCopyCurrent, m_nodeToCopy);

					updateCallPredToReturnPredsMapping(errorNWP.getFirst());


					doDefaultRedirecting(errorNWP);
					if (writeDetailedGraphs)
						m_gw.writeGraphAsImage(m_currentProcRoot,
								"graph_" + (++m_gwCounter) + "_ddr", m_nodeToCopyCurrent, m_nodeToCopy);

					redirect(errorNWP);
					if (writeDetailedGraphs)
						m_gw.writeGraphAsImage(m_currentProcRoot,
								"graph_" + (++m_gwCounter) + "_rd", m_nodeToCopyCurrent, m_nodeToCopy);

					//					m_gw.writeGraphAsImage(m_currentProcRoot, "graph_" + (++m_gwCounter) + "_cpddrrd");
				} else {
					if (isPEL) {
						AnnotatedProgramPoint lastApp = errorNWP.getFirst()[errorNWP.getFirst().length - 1];
						AnnotatedProgramPoint secondLastApp = errorNWP.getFirst()[errorNWP.getFirst().length - 2];
						secondLastApp.disconnectOutgoing(lastApp);
						//								secondLastApp.removeOutgoingNode(lastApp);
						//								lastApp.removeIncomingNode(secondLastApp);
						traceChecker.unlockSmtManager();
					} else {
						//								makeErrorTraceFromNW(errorNWP.getSecond());
						return Result.INCORRECT;
					}
				}
			}
		}
		//		return Result.UNKNOWN;
	}


	private void makeErrorTraceFromNW(NestedWord<CodeBlock> errorNW) {
		ArrayList<IElement> errorPathAL = new ArrayList<IElement>();
		Term[] errorPathFormulas = new Term[errorNW.length()];
		for (int i = 0; i < errorNW.length(); i++) { 
			errorPathAL.add(errorNW.getSymbolAt(i));
			errorPathFormulas[i] = errorNW.getSymbolAt(i).getTransitionFormula().getFormula();
		}
		m_errorTrace = new ErrorTrace(m_smtManager.getScript(), errorPathAL, errorPathFormulas);
	}

	private void copyNodes(
			Pair<AnnotatedProgramPoint[], NestedWord<CodeBlock>> errorNWP,
			IPredicate[] interpolants) {
		m_nodeToCopyCurrent.clear();

		AnnotatedProgramPoint[] appPath = errorNWP.getFirst();

		for (int i = 1; i < appPath.length - 1; i++) {
			TermVarsProc tvp = 
					m_smtManager.and(appPath[i].getPredicate(), interpolants[i-1]); //FIXME: indices may be incorrect
			IPredicate newPredicate = m_smtManager.newPredicate(tvp.getFormula(), 
					tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());

			//			AnnotatedProgramPoint copy = new AnnotatedProgramPoint(newPredicate, appPath[i].getProgramPoint());
			AnnotatedProgramPoint copy = new AnnotatedProgramPoint(appPath[i], newPredicate);
			m_programPointToItsAnnotatedPPs.get(copy.getProgramPoint()).add(copy);

			for (AnnotatedProgramPoint outNode : appPath[i].getOutgoingNodes()) {
				AnnotatedProgramPoint outApp = (AnnotatedProgramPoint) outNode;
				//				copy.addOutgoingNode(outApp, appPath[i].getOutgoingEdgeLabel(outApp));
				copy.connectOutgoing(outApp, appPath[i].getOutgoingEdgeLabel(outApp));
			}
			m_nodeToCopyCurrent.put(appPath[i], copy);


		}
		m_nodeToCopy.putAll(m_nodeToCopyCurrent);
	}


	private void updateCallPredToReturnPredsMapping(AnnotatedProgramPoint[] appPath) {
		//update the mapping in two respects:
		//1. callPredecessors on the appPath have to point to the new copy of the return predecessor, too
		//2. copies of callPredecessors point to the same nodes their copied node points to
		for (int i = 1; i < appPath.length - 1; i++) {
			ArrayList<AnnotatedProgramPoint> returnPreds = m_callPredToReturnPreds.get(appPath[i]);
			if (returnPreds != null) {//appPath[i] is a callPredecessor
				ArrayList<Pair<AnnotatedProgramPoint, AnnotatedProgramPoint>> toAdd = 
						new ArrayList<Pair<AnnotatedProgramPoint,AnnotatedProgramPoint>>();
				AnnotatedProgramPoint newCallPred = m_nodeToCopyCurrent.get(appPath[i]);//the copy of appPath[i] is a new CallPredecessor
				for (AnnotatedProgramPoint returnPred : returnPreds) {
					AnnotatedProgramPoint copy = m_nodeToCopyCurrent.get(returnPred);
					if (copy != null) {
						toAdd.add(new Pair<AnnotatedProgramPoint, AnnotatedProgramPoint>(appPath[i], copy));//1.
						toAdd.add(new Pair<AnnotatedProgramPoint, AnnotatedProgramPoint>(newCallPred, returnPred));//2.
						toAdd.add(new Pair<AnnotatedProgramPoint, AnnotatedProgramPoint>(newCallPred, copy));//2.
						//						addReturnPredToCP2RPsMapping(appPath[i], copy);//1.
						//						addReturnPredToCP2RPsMapping(newCallPred, returnPred); //2.
						//						addReturnPredToCP2RPsMapping(newCallPred, copy); //2.
					}
				}

				for (Pair<AnnotatedProgramPoint, AnnotatedProgramPoint> pair : toAdd) {
					addReturnPredToCP2RPsMapping(pair.getFirst(), pair.getSecond());
				}
			}
		}

		//duplicate the return edges (now that the values of the map have been updated with the new
		// returnPredecessors, it points to them and thus it suffices to walk over the copied nodes)
		for (int i = 1; i < appPath.length - 1; i++) {
			ArrayList<AnnotatedProgramPoint> returnPreds = m_callPredToReturnPreds.get(appPath[i]);
			//if appPath[i] is a CallPredecessor, the corresponding Returns must be duplicated
			//i.e. for each returnPredecessor, all outgoing returns that have the copied node as a
			//CallPredecessor now also must have the copy as a CallPredecessor
			if (returnPreds != null) {
				for (AnnotatedProgramPoint returnPred : returnPreds) {
					for (AnnotatedProgramPoint outNode : appPath[i].getOutgoingNodes()) {
						if (returnPred.outGoingReturnAppToCallPredContains(outNode, appPath[i])) {
							returnPred.addOutGoingReturnCallPred(outNode, m_nodeToCopy.get(appPath[i]));
						}
					}
				}
			}
		}
	}

	private void doDefaultRedirecting(
			Pair<AnnotatedProgramPoint[], NestedWord<CodeBlock>> errorNWP) {
		AnnotatedProgramPoint[] appPath = errorNWP.getFirst();

		//always redirect "procRoot -> appPath[0]" towards "procRoot -> nodeToCopy(appPath[0)"
		redirectEdge(m_currentProcRoot, appPath[1], m_nodeToCopyCurrent.get(appPath[1]));

		for (int i = 1; i < appPath.length - 2; i++) 
			redirectEdge(m_nodeToCopyCurrent.get(appPath[i]), 
					appPath[i+1], 
					m_nodeToCopyCurrent.get(appPath[i+1]));

		//always delete the edge from the last copy towards the error location
		m_nodeToCopyCurrent.get(appPath[appPath.length - 2]).
		disconnectOutgoing(appPath[appPath.length - 1]);
		//		removeOutgoingNode(appPath[appPath.length - 1]);
		//		appPath[appPath.length - 1].removeIncomingNode(m_nodeToCopyCurrent.get(appPath[appPath.length - 2]));

	}

	private void redirect(Pair<AnnotatedProgramPoint[],
			NestedWord<CodeBlock>> errorNWP) {
		AnnotatedProgramPoint[] appPath = errorNWP.getFirst();

		
		for (int i = 1; i < appPath.length - 2; i++) {
			ArrayList<AnnotatedProgramPoint[]> toRedirect = new ArrayList<AnnotatedProgramPoint[]>();
			ArrayList<AnnotatedProgramPoint[]> toRedirectReturns = new ArrayList<AnnotatedProgramPoint[]>();

//			AnnotatedProgramPoint copy = m_nodeToCopyCurrent.get(appPath[i]);
			for (AnnotatedProgramPoint inNode : appPath[i].getIncomingNodes()) {
				AnnotatedProgramPoint oldTarget = (AnnotatedProgramPoint) appPath[i];
				AnnotatedProgramPoint source = inNode;

				//old strategy:
//				AnnotatedProgramPoint possibleNewTarget = m_nodeToCopy.get(oldTarget); 

				//new strategy:
				ArrayList<AnnotatedProgramPoint> possibleTargets = new ArrayList<AnnotatedProgramPoint>();

				for (int j = 1; j <= i; j++) 
					if (appPath[j].getProgramPoint().equals(oldTarget.getProgramPoint())) 
						possibleTargets.add(m_nodeToCopy.get(appPath[j]));

				for (AnnotatedProgramPoint possibleNewTarget : possibleTargets) {

					LBool isInductive = null;
					if (possibleNewTarget != null) {
						CodeBlock statement = source.getOutgoingEdgeLabel(oldTarget);
						if (statement instanceof Summary)
							continue;
						else if (!(statement instanceof Return)) {
							if (statement instanceof Call) 
								isInductive = m_smtManager.isInductiveCall(
										source.getPredicate(), 
										(Call) statement, 
										possibleNewTarget.getPredicate());
							else 
								isInductive = m_smtManager.isInductive(
										source.getPredicate(), statement, possibleNewTarget.getPredicate());

							if (isInductive == LBool.UNSAT) {
								toRedirect.add(new AnnotatedProgramPoint[]{source, oldTarget, possibleNewTarget});
							//							redirectEdge(copy, outApp, copyOfOutApp);
							}
							else 
								appendNewPseudoErrorLocation(source, 
										source.getOutgoingEdgeLabel(oldTarget), 
										possibleNewTarget.getPredicate());
						} else if (statement instanceof Return) {
							HashSet<AnnotatedProgramPoint> callPreds = source.getCallPredsOfOutgoingReturnTarget(oldTarget);

							for (AnnotatedProgramPoint callPred : callPreds) {
								isInductive = m_smtManager.isInductiveReturn(
										source.getPredicate(), 
										callPred.getPredicate(),
										(Return) statement, 
										possibleNewTarget.getPredicate());
								if (isInductive == LBool.UNSAT) {
									toRedirectReturns.add(new AnnotatedProgramPoint[]{source, callPred, oldTarget, possibleNewTarget});
								//								redirectReturn(copy, callPred, outApp, copyOfOutApp);
								}
							}
							//no PseudoErrorLocations after Returns, right?
						}
					}
					if (isInductive == LBool.UNSAT)
						break;
				}
			}
			for (AnnotatedProgramPoint[] appA : toRedirect) 
				redirectEdge(appA[0], appA[1], appA[2]);
			for (AnnotatedProgramPoint[] appA : toRedirectReturns) 
				redirectReturn(appA[0], appA[1], appA[2], appA[3]);
			//
		}
	}

	/**
	 * Redirect a return edge with the CallPredecessor callPred copy-->outApp towards copyOfOutApp. 
	 * This is special for Returns as they have a special data structure.
	 * @param copy
	 * @param callPred
	 * @param outApp
	 * @param copyOfOutApp
	 */
	private void redirectReturn(AnnotatedProgramPoint copy,
			AnnotatedProgramPoint callPred, AnnotatedProgramPoint outApp, AnnotatedProgramPoint copyOfOutApp) {

		assert (copy.getOutgoingEdgeLabel(outApp) instanceof Return);
		assert (copy.getCallPredsOfOutgoingReturnTarget(outApp).size() >=1);

		//add new return edge
		if (!(copy.getOutgoingEdgeLabel(copyOfOutApp) instanceof Return))
			copy.connectOutgoing(copyOfOutApp, copy.getOutgoingEdgeLabel(outApp));

		copy.addOutGoingReturnCallPred(copyOfOutApp, callPred);


		//delete old return edge
		if (copy.getCallPredsOfOutgoingReturnTarget(outApp).size() == 1) 
			copy.disconnectOutgoing(outApp);

		copy.removeOutgoingReturnCallPred(outApp, callPred);
	}

	boolean m_usePseudoErrorLocations = false; 
//	right now, this causes a ConcurrentModificationException..
	private void appendNewPseudoErrorLocation(AnnotatedProgramPoint node,
			CodeBlock codeBlock, IPredicate predicate) {
		if (!m_usePseudoErrorLocations)
			return;
		//		Predicate newPredicate = m_smtManager.not(predicate); //will be negated implicitly by checkTrace
		if (m_smtManager.isInductive(node.getPredicate(), codeBlock, predicate) == LBool.UNSAT)
			return;

		AnnotatedProgramPoint pEL = 
				new AnnotatedProgramPoint(predicate, m_pELProgramPoint, true);
		node.connectIncoming(pEL, codeBlock);
		//		node.addOutgoingNode(pEL, codeBlock);
		//		pEL.addIncomingNode(node, codeBlock);
	}

	/*
	 * assuming there are no parallel edges
	 */
	private void redirectEdge(AnnotatedProgramPoint source, AnnotatedProgramPoint oldTarget,
			AnnotatedProgramPoint newTarget) {
		source.connectOutgoing(newTarget, source.getOutgoingEdgeLabel(oldTarget));
		oldTarget.disconnectIncoming(source);
		//		source.addOutgoingNode(newTarget, source.getOutgoingEdgeLabel(oldTarget));
		//		source.removeOutgoingNode(oldTarget);
		//		oldTarget.removeIncomingNode(source);
		//		newTarget.addIncomingNode(source, source.getOutgoingEdgeLabel(newTarget));
	}


	private void addReturnPredToCP2RPsMapping(
			AnnotatedProgramPoint callPred,
			AnnotatedProgramPoint returnPred) {
		ArrayList<AnnotatedProgramPoint> returnPreds = m_callPredToReturnPreds.get(callPred);
		if (returnPreds == null)
			returnPreds = new ArrayList<AnnotatedProgramPoint>();
		returnPreds.add(returnPred);
		m_callPredToReturnPreds.put(callPred, returnPreds);
	}

	private PrintWriter dumpInitialize() {
		File file = 
				new File(m_taPrefs.dumpPath() + "/" + ".txt");
		FileWriter fileWriter;
		try {
			fileWriter = new FileWriter(file);
			return new PrintWriter(fileWriter);
		} catch (IOException e) {
			e.printStackTrace();
		} 
		return null;
	}

	ImpRootNode getRoot() {
		return m_graphRoot;
	}

	private void reportResult(IResult res) {
		UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID, res);
	}

	// --------------------------------------------------
	// -------------- interface stuff -------------------
	// --------------------------------------------------

	@Override
	public void finish() {

	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	@Override
	public void init() {

	}

	@Override
	public boolean performedChanges() {
		return false;
	}

}
