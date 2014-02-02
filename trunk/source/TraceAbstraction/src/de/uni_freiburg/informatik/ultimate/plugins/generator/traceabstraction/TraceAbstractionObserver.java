package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.location.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Backtranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.boogie.BoogieProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.result.BackTranslationWorkaround;
import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.result.Check;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.GenericResultAtElement;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.InvariantResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.ProcedureContractResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;


/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class TraceAbstractionObserver implements IUnmanagedObserver {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.s_PLUGIN_ID);
	/**
	 * Root Node of this Ultimate model. I use this to store information that
	 * should be passed to the next plugin. The Successors of this node exactly
	 * the initial nodes of procedures.
	 */
	private IElement m_graphroot = null;
	private int m_OverallIterations;
	private int m_OverallBiggestAbstraction;
	private long m_OverallDeadEndRemovalTime;
	private long m_OverallMinimizationTime;
	private int m_OverallStatesRemovedByMinimization;
	private Result m_OverallResult;
	private IElement m_Artifact;
	private long m_StartingTime;
	

	@Override
	public boolean process(IElement root) {
		m_StartingTime = System.currentTimeMillis();
		RootAnnot rootAnnot = ((RootNode) root).getRootAnnot();
		TAPreferences taPrefs = new TAPreferences();
		
		String settings = "Automizer settings:";
		settings += " Hoare:"+ taPrefs.computeHoareAnnotation();
		settings += " " + (taPrefs.differenceSenwa() ? "SeNWA" : "NWA");
		settings += " Interpolation:"+ taPrefs.interpolation();
		settings += " Determinization: " + taPrefs.determinization();
		settings += " Timeout:" + taPrefs.timeout();
		System.out.println(settings);

		SmtManager smtManager = new SmtManager(rootAnnot.getBoogie2SMT(),
				rootAnnot.getGlobalVars(),
				rootAnnot.getModGlobVarManager());
		TraceAbstractionBenchmarks timingStatistics = new TraceAbstractionBenchmarks(smtManager);

		Map<String, Collection<ProgramPoint>> proc2errNodes = rootAnnot.getErrorNodes();
		Collection<ProgramPoint> errNodesOfAllProc = new ArrayList<ProgramPoint>();
		for (Collection<ProgramPoint> errNodeOfProc : proc2errNodes.values()) {
			errNodesOfAllProc.addAll(errNodeOfProc);
		}

		setTimeout(taPrefs);
		m_OverallIterations = 0;
		m_OverallBiggestAbstraction = 0;
		m_OverallResult = Result.SAFE;
		m_Artifact = null;

		if (taPrefs.allErrorLocsAtOnce()) {
			String name = "AllErrorsAtOnce";
			iterate(name, (RootNode) root, taPrefs, smtManager, timingStatistics, errNodesOfAllProc);
		} else {
			for (ProgramPoint errorLoc : errNodesOfAllProc) {
				String name = errorLoc.getLocationName();
				ArrayList<ProgramPoint> errorLocs = new ArrayList<ProgramPoint>(1);
				errorLocs.add(errorLoc);
				UltimateServices.getInstance().setSubtask(errorLoc.toString());
				iterate(name, (RootNode) root, taPrefs, smtManager, timingStatistics, errorLocs);
			}
		}

		s_Logger.debug("Compute Hoare Annotation: " + taPrefs.computeHoareAnnotation());
		s_Logger.debug("Overall result: " + m_OverallResult);
		s_Logger.debug("Continue processing: " + UltimateServices.getInstance().continueProcessing());
		if (taPrefs.computeHoareAnnotation() && m_OverallResult != Result.TIMEOUT 
				&& UltimateServices.getInstance().continueProcessing()) {
			assert (smtManager.cfgInductive((RootNode) root));
			
			List<ITranslator<?, ?, ?, ?>> translator_sequence = 
					UltimateServices.getInstance().getTranslatorSequence();
			
			Map<String, ProgramPoint> finalNodes = rootAnnot.getExitNodes();
			for (String proc : finalNodes.keySet()) {
				if (isAuxilliaryProcedure(proc)) {
					continue;
				}
				ProgramPoint finalNode = finalNodes.get(proc);
				HoareAnnotation hoare = getHoareAnnotation(finalNode);
				if (hoare != null) {
					Procedure implementation = rootAnnot.getProcedures().get(
							proc);
					ProcedureContractResult<RcfgElement, Expression> invResult = 
							new ProcedureContractResult<RcfgElement, Expression>(
							finalNode,
							Activator.s_PLUGIN_NAME,
							translator_sequence,
							implementation.getLocation().getOrigin(),
							proc);
					Term formula = hoare.getFormula();
					Expression expr = rootAnnot.getBoogie2Smt().translate(
							formula);
					invResult.setInvariant(expr);
					String ppExpr = BackTranslationWorkaround.backtranslate(
							translator_sequence, expr);
					invResult.setLongDescription(ppExpr);
					s_Logger.warn("Derived contract for procedure " + proc
							+ ": " + formula.toString() + "   "
							+ ppExpr);
					reportResult(invResult);
				}
			}
			Map<ProgramPoint, ILocation> loopLocations = rootAnnot
					.getLoopLocations();
			for (ProgramPoint locNode : loopLocations.keySet()) {
				assert (locNode.getBoogieASTNode() != null) : "locNode without BoogieASTNode";
				HoareAnnotation hoare = getHoareAnnotation(locNode);
				if (hoare != null) {
					InvariantResult<RcfgElement, Expression> invResult = 
							new InvariantResult<RcfgElement, Expression>(
							locNode,
							Activator.s_PLUGIN_NAME,
							translator_sequence,
							loopLocations.get(locNode).getOrigin());
					Term formula = hoare.getFormula();
					Expression expr = rootAnnot.getBoogie2Smt().translate(
							formula);
					invResult.setInvariant(expr);
					String ppExpr = BackTranslationWorkaround.backtranslate(
							translator_sequence, expr);
					invResult.setLongDescription(ppExpr);
					s_Logger.warn("Derived loop invarinat at "
							+ locNode.getBoogieASTNode().getLocation() + ": "
							+ formula.toString() + expr + "   "
							+ ppExpr);
					reportResult(invResult);
				}
			}
		}

		String stat = "";
		stat += "Statistics:  ";
		stat += " Iterations " + m_OverallIterations + ".";
		stat += " CFG has ";
		stat += rootAnnot.getNumberOfProgramPoints();
		stat += " locations,";
		stat += errNodesOfAllProc.size();
		stat += " error locations.";
		stat += " Cover queries: ";
		stat += smtManager.getTrivialCoverQueries() + " tivial, ";
		stat += smtManager.getNontrivialCoverQueries() + " nontrivial.";	
		stat += " EdgeCheck queries: ";
		stat += smtManager.getTrivialEdgeCheckQueries() + " tivial, ";
		stat += smtManager.getLazyEdgeCheckQueries() + " lazy, ";
		stat += smtManager.getNontrivialEdgeCheckQueries() + " nontrivial.";
		stat += " Satisfiability queries: ";
		stat += smtManager.getTrivialSatQueries() + " tivial, ";
		stat += smtManager.getNontrivialSatQueries() + " nontrivial.";
		stat += " DeadEndRemovalTime: " + m_OverallDeadEndRemovalTime;
		stat += " Minimization removed " + m_OverallStatesRemovedByMinimization;
		stat += " in time " + m_OverallMinimizationTime;
		stat += " Biggest abstraction had ";
		stat += m_OverallBiggestAbstraction;
		stat += " states.";
		s_Logger.warn(stat);
		s_Logger.warn("PC#: " + smtManager.getInterpolQueries());
		s_Logger.warn("TIME#: " + smtManager.getInterpolQuriesTime());
		s_Logger.warn("ManipulationTIME#: " + smtManager.getTraceCheckTime());
		s_Logger.warn("EC#: " + smtManager.getNontrivialEdgeCheckQueries());
		s_Logger.warn("TIME#: " + smtManager.getSatCheckTime());
		s_Logger.warn("ManipulationTIME#: "	+ smtManager.getSatCheckTime());
		s_Logger.warn(timingStatistics.printBenchmarkResults());
		switch (m_OverallResult) {
		case SAFE:
//			s_Logger.warn("Program is correct");
//			ResultNotifier.programCorrect();
			break;
		case UNSAFE:
//			s_Logger.warn("Program is incorrect");
//			ResultNotifier.programIncorrect();
			break;
		case TIMEOUT:
			s_Logger.warn("Insufficient iterations to proof correctness");
//			ResultNotifier
//					.programUnknown("Insufficient iterations to proof correctness");
			break;
		case UNKNOWN:
			s_Logger.warn("Program might be incorrect, check conterexample.");
//			ResultNotifier.programUnknown("Program might be incorrect, check"
//					+ " conterexample.");
			break;
		}

		m_graphroot = m_Artifact;

		return false;
	}

	public static void setTimeout(TAPreferences taPrefs) {
		int timeoutInPreferences = taPrefs.timeout();
		if (timeoutInPreferences == 0) {
			// do not set any timout
		} else {
			long timoutMilliseconds = timeoutInPreferences * 1000L;
			UltimateServices.getInstance().setDeadline(
					System.currentTimeMillis() + timoutMilliseconds);
		}
	}

	private void iterate(String name, RootNode root, TAPreferences taPrefs,
			SmtManager smtManager, TraceAbstractionBenchmarks timingStatistics,
			Collection<ProgramPoint> errorLocs) {
		AbstractCegarLoop abstractCegarLoop;
		if (taPrefs.interpolantAutomaton() == InterpolantAutomaton.TOTALINTERPOLATION) {
			abstractCegarLoop = new CegarLoopSequentialWithBackedges(name, 
					root, smtManager, timingStatistics,taPrefs, errorLocs);
		} else {
			abstractCegarLoop = new BasicCegarLoop(name, 
					root, smtManager, timingStatistics,taPrefs, errorLocs);
		}

		Result result = abstractCegarLoop.iterate();

		m_OverallIterations += abstractCegarLoop.m_Iteration;
		if (abstractCegarLoop.m_BiggestAbstractionSize > m_OverallBiggestAbstraction) {
			m_OverallBiggestAbstraction = abstractCegarLoop.m_BiggestAbstractionSize;
		}
		m_OverallDeadEndRemovalTime += abstractCegarLoop.m_DeadEndRemovalTime;
		m_OverallMinimizationTime += abstractCegarLoop.m_MinimizationTime;
		m_OverallStatesRemovedByMinimization += abstractCegarLoop.m_StatesRemovedByMinimization;

		switch (result) {
		case SAFE:
			reportPositiveResult(errorLocs);
			break;
		case UNSAFE: 
			{
				RcfgProgramExecution pe = abstractCegarLoop.getRcfgProgramExecution();
				reportCounterexampleResult(pe);
				m_OverallResult = result;
				break;
			}
		case TIMEOUT:
			reportTimoutResult(errorLocs);
			if (m_OverallResult != Result.UNSAFE) {
				m_OverallResult = result;
			}
			break;
		case UNKNOWN: 
			{
				RcfgProgramExecution pe = abstractCegarLoop.getRcfgProgramExecution();
				reportUnproveableResult(pe);
				if (m_OverallResult != Result.UNSAFE) {
					m_OverallResult = result;
				}
				break;
			}
		}
		if (taPrefs.computeHoareAnnotation()) {
			s_Logger.debug("Computing Hoare annotation of CFG");
			abstractCegarLoop.computeCFGHoareAnnotation();
		} else {
			s_Logger.debug("Ommiting computation of Hoare annotation");
			
		}
		m_Artifact = abstractCegarLoop.getArtifact();
		reportTimingStatistics(root, timingStatistics);	
	}
	
	private void reportPositiveResult(Collection<ProgramPoint> errorLocs) {
		if (errorLocs.isEmpty()) {
			String shortDescription = "No specification checked";
			String longDescription = "We were not able to verify any" +
					" specifiation because the program does not contain any specification.";
			GenericResult gr = new GenericResult(
					Activator.s_PLUGIN_NAME, 
					shortDescription,
					longDescription,
					GenericResultAtElement.Severity.WARNING);
			s_Logger.warn(shortDescription + " " + longDescription);
			reportResult(gr);
		} else {
			for (ProgramPoint errorLoc : errorLocs) {
				ILocation origin = errorLoc.getBoogieASTNode().getLocation().getOrigin();
				PositiveResult<RcfgElement> pResult = new PositiveResult<RcfgElement>(
						errorLoc,
						Activator.s_PLUGIN_NAME,
						UltimateServices.getInstance().getTranslatorSequence(),
						origin);
				String pMessage = getCheckedSpecification(errorLoc).getPositiveMessage();
				pResult.setShortDescription(pMessage);
				pMessage += " (line " + origin.getStartLine() + ")";			
				reportResult(pResult);
				s_Logger.warn(pMessage);
			}
		}
	}
	
	private void reportCounterexampleResult(RcfgProgramExecution pe) {
		ProgramPoint errorPP = getErrorPP(pe);
		List<ILocation> failurePath = pe.getLocationList();
		ILocation origin = errorPP.getPayload().getLocation().getOrigin();
		
		List<ITranslator<?, ?, ?, ?>> translatorSequence = UltimateServices.getInstance().getTranslatorSequence();
		if (pe.isOverapproximation()) {
			reportUnproveableResult(pe);
			return;
		}
		CounterExampleResult<RcfgElement> ctxRes = new CounterExampleResult<RcfgElement>(
				errorPP,
				Activator.s_PLUGIN_NAME,
				translatorSequence,
				origin, null);
		String ctxMessage = getCheckedSpecification(errorPP).getNegativeMessage();
		ctxRes.setShortDescription(ctxMessage);		
		ctxMessage += " (line " + origin.getStartLine() + ")";
		Backtranslator backtrans = (Backtranslator) translatorSequence.get(translatorSequence.size()-1);
		BoogieProgramExecution bpe = (BoogieProgramExecution) backtrans.translateProgramExecution(pe);
		ctxRes.setLongDescription(bpe.toString());
		ctxRes.setFailurePath(bpe.getLocationSequence());
		ctxRes.setValuation(bpe.getValuation());
		reportResult(ctxRes);
		s_Logger.warn(ctxMessage);
	}
	
	private void reportTimoutResult(Collection<ProgramPoint> errorLocs) {
		for (ProgramPoint errorLoc : errorLocs) {
			ILocation origin = errorLoc.getBoogieASTNode().getLocation().getOrigin();
			String timeOutMessage = "Unable to prove that " +
					getCheckedSpecification(errorLoc).getPositiveMessage();
			timeOutMessage += " (line " + origin.getStartLine() + ")";
			TimeoutResult<RcfgElement> timeOutRes = new TimeoutResult<RcfgElement>(
					errorLoc,
					Activator.s_PLUGIN_NAME,
					UltimateServices.getInstance().getTranslatorSequence(),
					origin,
					timeOutMessage);
			reportResult(timeOutRes);
			s_Logger.warn(timeOutMessage);
		}
	}
		
	private void reportUnproveableResult(RcfgProgramExecution pe) {
		ProgramPoint errorPP = getErrorPP(pe);
		List<ILocation> failurePath = pe.getLocationList();
		ILocation origin = errorPP.getPayload().getLocation().getOrigin();
		UnprovableResult<RcfgElement> uknRes = new UnprovableResult<RcfgElement>(
				errorPP,
				Activator.s_PLUGIN_NAME,
				UltimateServices.getInstance().getTranslatorSequence(),
				origin);
		uknRes.setFailurePath(failurePath);
		String uknMessage = "Unable to prove that " + 
				getCheckedSpecification(errorPP).getPositiveMessage();
		uknRes.setShortDescription(uknMessage);
		uknMessage += " (line " + origin.getStartLine() + ")";
		uknRes.setLongDescription(failurePath.toString());
		reportResult(uknRes);
		s_Logger.warn(uknMessage);
	}
	
	private void reportTimingStatistics(RootNode root, TraceAbstractionBenchmarks timingStatistics) {
		String shortDescription = "Ultimate Automizer runtime statistics";
		long time = System.currentTimeMillis() - m_StartingTime;
		if (root.getOutgoingNodes().isEmpty()) {
			s_Logger.warn("No procedure was checked. I don't know any location."
					+ "Will not report any timing statistics.");
			return;
		}
		RCFGNode someNode = root.getOutgoingNodes().iterator().next();
		BenchmarkResult res = new 
				BenchmarkResult(Activator.s_PLUGIN_NAME, 
				shortDescription, timingStatistics);
		s_Logger.warn(res.getLongDescription());

//		String longDescription = "Ultimate Automizer took " + time + "ms";
//		longDescription += timingStatistics.printTimingStatistics();
		reportResult(res);
	}
	
	/**
	 * Return the checked specification that is checked at the error location.
	 */
	private static Check getCheckedSpecification(ProgramPoint errorLoc) {
		if (errorLoc.getPayload().hasAnnotation()) {
			IAnnotations check = errorLoc.getPayload().getAnnotations().get(Check.getIdentifier());
			return (Check) check;
		}
		return errorLoc.getBoogieASTNode().getLocation().getOrigin().checkedSpecification();
	}
	
	
	private static boolean isAuxilliaryProcedure(String proc) {
		if (proc.equals("ULTIMATE.init") || proc.equals("ULTIMATE.start")) {
			return true;
		} else {
			return false;
		}
	}


	// Term simplify(Term term, RootNode rootNode) {
	// Script script = rootAnnot.getScript();
	// String unsimp = term.toStringDirect();
	// Term result = new SimplifyDDA(script, s_Logger).getSimplifiedTerm(term);
	// String simp = result.toStringDirect();
	// return result;
	// }

	private void reportResult(IResult res) {
		UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID, res);
	}

	/**
	 * @return the root of the CFG.
	 */
	public IElement getRoot() {
		return m_graphroot;
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

	public static HoareAnnotation getHoareAnnotation(ProgramPoint programPoint) {
		return ((HoareAnnotation) programPoint.getPayload().getAnnotations()
				.get(Activator.s_PLUGIN_ID));
	}
	
	public ProgramPoint getErrorPP(RcfgProgramExecution rcfgProgramExecution) {
		int lastPosition = rcfgProgramExecution.getLength() - 1;
		CodeBlock last = rcfgProgramExecution.getTraceElement(lastPosition);
		ProgramPoint errorPP = (ProgramPoint) last.getTarget();
		return errorPP;
	}

}
