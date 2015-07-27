package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.LanguageOperation;
import de.uni_freiburg.informatik.ultimate.result.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.InvariantResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.ProcedureContractResult;
import de.uni_freiburg.informatik.ultimate.result.ResultUtil;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

public class TraceAbstractionStarter {
	
	private final Logger m_Logger;
	private final IUltimateServiceProvider m_Services;
	private final IToolchainStorage m_ToolchainStorage;

	public TraceAbstractionStarter(IUltimateServiceProvider services, 
			IToolchainStorage storage, RootNode rcfgRootNode, 
			NestedWordAutomaton<WitnessEdge, WitnessNode> witnessAutomaton) {
		m_Services = services;
		m_ToolchainStorage = storage;
		m_Logger = m_Services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		runCegarLoops(rcfgRootNode, witnessAutomaton);
	}
	
	/**
	 * Root Node of this Ultimate model. I use this to store information that
	 * should be passed to the next plugin. The Successors of this node exactly
	 * the initial nodes of procedures.
	 */
	private IElement m_RootOfNewModel = null;
	private Result m_OverallResult;
	private IElement m_Artifact;
	
	
	
	private void runCegarLoops(RootNode rcfgRootNode, NestedWordAutomaton<WitnessEdge, WitnessNode> witnessAutomaton) {
		RootAnnot rootAnnot = rcfgRootNode.getRootAnnot();
		TAPreferences taPrefs = new TAPreferences();

		String settings = "Automizer settings:";
		settings += " Hoare:" + taPrefs.computeHoareAnnotation();
		settings += " " + (taPrefs.differenceSenwa() ? "SeNWA" : "NWA");
		settings += " Interpolation:" + taPrefs.interpolation();
		settings += " Determinization: " + taPrefs.interpolantAutomatonEnhancement();
		System.out.println(settings);

		SmtManager smtManager = new SmtManager(rootAnnot.getBoogie2SMT(), rootAnnot.getModGlobVarManager(), m_Services);
		TraceAbstractionBenchmarks traceAbstractionBenchmark = new TraceAbstractionBenchmarks(rootAnnot);

		Map<String, Collection<ProgramPoint>> proc2errNodes = rootAnnot.getErrorNodes();
		Collection<ProgramPoint> errNodesOfAllProc = new ArrayList<ProgramPoint>();
		for (Collection<ProgramPoint> errNodeOfProc : proc2errNodes.values()) {
			errNodesOfAllProc.addAll(errNodeOfProc);
		}

		m_OverallResult = Result.SAFE;
		m_Artifact = null;

		if (taPrefs.allErrorLocsAtOnce()) {
			String name = "AllErrorsAtOnce";
			iterate(name, rcfgRootNode, taPrefs, smtManager, traceAbstractionBenchmark, errNodesOfAllProc, witnessAutomaton);
		} else {
			for (ProgramPoint errorLoc : errNodesOfAllProc) {
				String name = errorLoc.getLocationName();
				ArrayList<ProgramPoint> errorLocs = new ArrayList<ProgramPoint>(1);
				errorLocs.add(errorLoc);
				m_Services.getProgressMonitorService().setSubtask(errorLoc.toString());
				iterate(name, rcfgRootNode, taPrefs, smtManager, traceAbstractionBenchmark, errorLocs, witnessAutomaton);
			}
		}
		if (m_OverallResult == Result.SAFE) {
			final String longDescription;
			if (errNodesOfAllProc.isEmpty()) {
				longDescription = "We were not able to verify any"
						+ " specifiation because the program does not contain any specification.";
			} else {
				longDescription = errNodesOfAllProc.size() + " specifications checked. All of them hold";
			}
			AllSpecificationsHoldResult result = new AllSpecificationsHoldResult(Activator.s_PLUGIN_NAME, longDescription);
			reportResult(result);
		}

		m_Logger.debug("Compute Hoare Annotation: " + taPrefs.computeHoareAnnotation());
		m_Logger.debug("Overall result: " + m_OverallResult);
		m_Logger.debug("Continue processing: " + m_Services.getProgressMonitorService().continueProcessing());
		if (taPrefs.computeHoareAnnotation() && m_OverallResult != Result.TIMEOUT
				&& m_Services.getProgressMonitorService().continueProcessing()) {
			assert (smtManager.cfgInductive(rcfgRootNode));

			IBacktranslationService translator_sequence = m_Services.getBacktranslationService();

			Map<String, ProgramPoint> finalNodes = rootAnnot.getExitNodes();
			for (String proc : finalNodes.keySet()) {
				if (isAuxilliaryProcedure(proc)) {
					continue;
				}
				ProgramPoint finalNode = finalNodes.get(proc);
				HoareAnnotation hoare = getHoareAnnotation(finalNode);
				if (hoare != null) {
					Term formula = hoare.getFormula();
					Expression expr = rootAnnot.getBoogie2SMT().getTerm2Expression().translate(formula);
					ProcedureContractResult<RcfgElement, Expression> result = new ProcedureContractResult<RcfgElement, Expression>(
							Activator.s_PLUGIN_NAME, finalNode, translator_sequence, proc, expr);
					// s_Logger.warn(result.getShortDescription());
					reportResult(result);
				}
			}
			Map<ProgramPoint, ILocation> loopLocations = rootAnnot.getLoopLocations();
			for (ProgramPoint locNode : loopLocations.keySet()) {
				assert (locNode.getBoogieASTNode() != null) : "locNode without BoogieASTNode";
				HoareAnnotation hoare = getHoareAnnotation(locNode);
				if (hoare != null) {
					Term formula = hoare.getFormula();
					Expression expr = rootAnnot.getBoogie2SMT().getTerm2Expression().translate(formula);
					InvariantResult<RcfgElement, Expression> invResult = new InvariantResult<RcfgElement, Expression>(
							Activator.s_PLUGIN_NAME, locNode, translator_sequence, expr);
					// s_Logger.warn(invResult.getLongDescription());
					reportResult(invResult);
				}
			}
		}
		reportBenchmark(traceAbstractionBenchmark);
		switch (m_OverallResult) {
		case SAFE:
			// s_Logger.warn("Program is correct");
			// ResultNotifier.programCorrect();
			break;
		case UNSAFE:
			// s_Logger.warn("Program is incorrect");
			// ResultNotifier.programIncorrect();
			break;
		case TIMEOUT:
			m_Logger.warn("Timeout");
			// ResultNotifier
			// .programUnknown("Timeout");
			break;
		case UNKNOWN:
			m_Logger.warn("Unable to decide correctness. Please check the following counterexample manually.");
			// ResultNotifier.programUnknown("Program might be incorrect, check"
			// + " conterexample.");
			break;
		}

		m_RootOfNewModel = m_Artifact;
	}
	
	
	private void iterate(String name, RootNode root, TAPreferences taPrefs, SmtManager smtManager,
			TraceAbstractionBenchmarks taBenchmark, Collection<ProgramPoint> errorLocs, NestedWordAutomaton<WitnessEdge, WitnessNode> witnessAutomaton) {
		BasicCegarLoop basicCegarLoop;
		LanguageOperation languageOperation = (new UltimatePreferenceStore(Activator.s_PLUGIN_ID)).getEnum(
				TraceAbstractionPreferenceInitializer.LABEL_LANGUAGE_OPERATION,
				LanguageOperation.class);
		if (languageOperation == LanguageOperation.DIFFERENCE) {		
			if (taPrefs.interpolantAutomaton() == InterpolantAutomaton.TOTALINTERPOLATION) {
				basicCegarLoop = new CegarLoopSWBnonRecursive(name, root, smtManager, taBenchmark, taPrefs, errorLocs,
						taPrefs.interpolation(), taPrefs.computeHoareAnnotation(), m_Services, m_ToolchainStorage);
				// abstractCegarLoop = new CegarLoopSequentialWithBackedges(name,
				// root, smtManager, timingStatistics,taPrefs, errorLocs);
			} else {
				basicCegarLoop = new BasicCegarLoop(name, root, smtManager, taPrefs, errorLocs, taPrefs.interpolation(),
						taPrefs.computeHoareAnnotation(), m_Services, m_ToolchainStorage);
			}
		} else {
			basicCegarLoop = new IncrementalInclusionCegarLoop(name, root, smtManager, taPrefs, errorLocs, taPrefs.interpolation(), 
					taPrefs.computeHoareAnnotation(), m_Services, m_ToolchainStorage, languageOperation);
		}
		basicCegarLoop.setWitnessAutomaton(witnessAutomaton);

		Result result = basicCegarLoop.iterate();
		basicCegarLoop.finish();
		CegarLoopBenchmarkGenerator cegarLoopBenchmarkGenerator = basicCegarLoop.getCegarLoopBenchmark();
		cegarLoopBenchmarkGenerator.stop(CegarLoopBenchmarkType.s_OverallTime);
		taBenchmark.aggregateBenchmarkData(cegarLoopBenchmarkGenerator);

		switch (result) {
		case SAFE:
			reportPositiveResults(errorLocs);
			break;
		case UNSAFE: {
			RcfgProgramExecution pe = basicCegarLoop.getRcfgProgramExecution();
			reportCounterexampleResult(pe);
			m_OverallResult = result;
			break;
		}
		case TIMEOUT:
			reportTimeoutResult(errorLocs);
			if (m_OverallResult != Result.UNSAFE) {
				m_OverallResult = result;
			}
			break;
		case UNKNOWN: {
			RcfgProgramExecution pe = basicCegarLoop.getRcfgProgramExecution();
			reportUnproveableResult(pe);
			if (m_OverallResult != Result.UNSAFE) {
				m_OverallResult = result;
			}
			break;
		}
		}
		if (taPrefs.computeHoareAnnotation() && m_OverallResult == Result.SAFE) {
			m_Logger.debug("Computing Hoare annotation of CFG");
			basicCegarLoop.computeCFGHoareAnnotation();
			writeHoareAnnotationToLogger(root);
		} else {
			m_Logger.debug("Ommiting computation of Hoare annotation");

		}
		m_Artifact = basicCegarLoop.getArtifact();
	}

	private void writeHoareAnnotationToLogger(RootNode root) {
		for (Entry<String, Map<String, ProgramPoint>> proc2label2pp : root.getRootAnnot().getProgramPoints().entrySet()) {
			for (ProgramPoint pp : proc2label2pp.getValue().values()) {
				HoareAnnotation hoare = getHoareAnnotation(pp);
				if (hoare == null) {
					m_Logger.info("For program point  " + prettyPrintProgramPoint(pp)
							+ "  no Hoare annotation was computed.");
				} else {
					m_Logger.info("At program point  " + prettyPrintProgramPoint(pp)
							+ "  the Hoare annotation is:  " + hoare.getFormula());
				}
			}
		}
	}
	
	private static String prettyPrintProgramPoint(ProgramPoint pp) {
		int startLine = pp.getPayload().getLocation().getStartLine();
		int endLine = pp.getPayload().getLocation().getStartLine();
		StringBuilder sb = new StringBuilder();
		sb.append(pp);
		if (startLine == endLine) {
			sb.append("(line " + startLine + ")");
		} else {
			sb.append("(lines " + startLine + " " + endLine + ")");
		}
		return sb.toString();
	}


	private void reportPositiveResults(Collection<ProgramPoint> errorLocs) {
		for (ProgramPoint errorLoc : errorLocs) {
			PositiveResult<RcfgElement> pResult = new PositiveResult<RcfgElement>(Activator.s_PLUGIN_NAME,
					errorLoc, m_Services.getBacktranslationService());
			reportResult(pResult);
		}
	}

	private void reportCounterexampleResult(RcfgProgramExecution pe) {
		if (pe.isOverapproximation()) {
			reportUnproveableResult(pe);
			return;
		}
		reportResult(new CounterExampleResult<RcfgElement,CodeBlock, Expression>(getErrorPP(pe), Activator.s_PLUGIN_NAME,
				m_Services.getBacktranslationService(), pe));
	}

	private void reportTimeoutResult(Collection<ProgramPoint> errorLocs) {
		for (ProgramPoint errorLoc : errorLocs) {
			ILocation origin = errorLoc.getBoogieASTNode().getLocation().getOrigin();
			String timeOutMessage = "Unable to prove that "
					+ ResultUtil.getCheckedSpecification(errorLoc).getPositiveMessage();
			timeOutMessage += " (line " + origin.getStartLine() + ")";
			TimeoutResultAtElement<RcfgElement> timeOutRes = new TimeoutResultAtElement<RcfgElement>(errorLoc,
					Activator.s_PLUGIN_NAME, m_Services.getBacktranslationService(),
					timeOutMessage);
			reportResult(timeOutRes);
			// s_Logger.warn(timeOutMessage);
		}
	}

	private void reportUnproveableResult(RcfgProgramExecution pe) {
		ProgramPoint errorPP = getErrorPP(pe);
		UnprovableResult<RcfgElement, CodeBlock, Expression> uknRes = new UnprovableResult<RcfgElement, CodeBlock, Expression>(
				Activator.s_PLUGIN_NAME, errorPP, m_Services.getBacktranslationService(), pe);
		reportResult(uknRes);
	}

	private <T> void reportBenchmark(ICsvProviderProvider<T> benchmark) {
		String shortDescription = "Ultimate Automizer benchmark data";
		BenchmarkResult<T> res = new BenchmarkResult<T>(Activator.s_PLUGIN_NAME, shortDescription, benchmark);
		// s_Logger.warn(res.getLongDescription());

		reportResult(res);
	}

	private static boolean isAuxilliaryProcedure(String proc) {
		if (proc.equals("ULTIMATE.init") || proc.equals("ULTIMATE.start")) {
			return true;
		} else {
			return false;
		}
	}
	
	
	private void reportResult(IResult res) {
		m_Services.getResultService().reportResult(Activator.s_PLUGIN_ID, res);
	}

	/**
	 * @return the root of the CFG.
	 */
	public IElement getRootOfNewModel() {
		return m_RootOfNewModel;
	}
	
	
	
	public static HoareAnnotation getHoareAnnotation(ProgramPoint programPoint) {
		return ((HoareAnnotation) programPoint.getPayload().getAnnotations().get(Activator.s_PLUGIN_ID));
	}

	public ProgramPoint getErrorPP(RcfgProgramExecution rcfgProgramExecution) {
		int lastPosition = rcfgProgramExecution.getLength() - 1;
		CodeBlock last = rcfgProgramExecution.getTraceElement(lastPosition).getTraceElement();
		ProgramPoint errorPP = (ProgramPoint) last.getTarget();
		return errorPP;
	}

}
