package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.ExampleNWAFactory;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RCFGBacktranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.boogie.BoogieProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolantAutomaton;
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

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class TraceAbstractionObserver implements IUnmanagedObserver {

	private final Logger mLogger;
	private final IUltimateServiceProvider mServices;

	public TraceAbstractionObserver(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
	}

	/**
	 * Root Node of this Ultimate model. I use this to store information that
	 * should be passed to the next plugin. The Successors of this node exactly
	 * the initial nodes of procedures.
	 */
	private IElement m_graphroot = null;
	private Result m_OverallResult;
	private IElement m_Artifact;

	@Override
	public boolean process(IElement root) {
		
		//TODO: Now you can get instances of your library classes for the current toolchain like this: 
		//NWA is nevertheless very broken, as its static initialization prevents parallelism 
		//Surprisingly, this call lazily initializes the static fields of NWA Lib and, like magic, the toolchain works ...
		mServices.getServiceInstance(ExampleNWAFactory.class);

		
		RootAnnot rootAnnot = ((RootNode) root).getRootAnnot();
		TAPreferences taPrefs = new TAPreferences();

		String settings = "Automizer settings:";
		settings += " Hoare:" + taPrefs.computeHoareAnnotation();
		settings += " " + (taPrefs.differenceSenwa() ? "SeNWA" : "NWA");
		settings += " Interpolation:" + taPrefs.interpolation();
		settings += " Determinization: " + taPrefs.determinization();
		System.out.println(settings);

		SmtManager smtManager = new SmtManager(rootAnnot.getBoogie2SMT(), rootAnnot.getModGlobVarManager(), mServices);
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
			iterate(name, (RootNode) root, taPrefs, smtManager, traceAbstractionBenchmark, errNodesOfAllProc);
		} else {
			for (ProgramPoint errorLoc : errNodesOfAllProc) {
				String name = errorLoc.getLocationName();
				ArrayList<ProgramPoint> errorLocs = new ArrayList<ProgramPoint>(1);
				errorLocs.add(errorLoc);
				mServices.getProgressMonitorService().setSubtask(errorLoc.toString());
				iterate(name, (RootNode) root, taPrefs, smtManager, traceAbstractionBenchmark, errorLocs);
			}
		}

		mLogger.debug("Compute Hoare Annotation: " + taPrefs.computeHoareAnnotation());
		mLogger.debug("Overall result: " + m_OverallResult);
		mLogger.debug("Continue processing: " + mServices.getProgressMonitorService().continueProcessing());
		if (taPrefs.computeHoareAnnotation() && m_OverallResult != Result.TIMEOUT
				&& mServices.getProgressMonitorService().continueProcessing()) {
			assert (smtManager.cfgInductive((RootNode) root));

			List<ITranslator<?, ?, ?, ?>> translator_sequence = mServices.getBacktranslationService().getTranslatorSequence();

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
			mLogger.warn("Timeout");
			// ResultNotifier
			// .programUnknown("Timeout");
			break;
		case UNKNOWN:
			mLogger.warn("Unable to decide correctness. Please check the following counterexample manually.");
			// ResultNotifier.programUnknown("Program might be incorrect, check"
			// + " conterexample.");
			break;
		}

		m_graphroot = m_Artifact;

		return false;
	}

	private void iterate(String name, RootNode root, TAPreferences taPrefs, SmtManager smtManager,
			TraceAbstractionBenchmarks taBenchmark, Collection<ProgramPoint> errorLocs) {
		BasicCegarLoop basicCegarLoop;
		if (taPrefs.interpolantAutomaton() == InterpolantAutomaton.TOTALINTERPOLATION) {
			basicCegarLoop = new CegarLoopSWBnonRecursive(name, root, smtManager, taBenchmark, taPrefs, errorLocs,
					taPrefs.interpolation(), taPrefs.computeHoareAnnotation(), mServices);
			// abstractCegarLoop = new CegarLoopSequentialWithBackedges(name,
			// root, smtManager, timingStatistics,taPrefs, errorLocs);
		} else {
			basicCegarLoop = new BasicCegarLoop(name, root, smtManager, taPrefs, errorLocs, taPrefs.interpolation(),
					taPrefs.computeHoareAnnotation(), mServices);
		}

		Result result = basicCegarLoop.iterate();
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
			reportTimoutResult(errorLocs);
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
		if (taPrefs.computeHoareAnnotation()) {
			mLogger.debug("Computing Hoare annotation of CFG");
			basicCegarLoop.computeCFGHoareAnnotation();
		} else {
			mLogger.debug("Ommiting computation of Hoare annotation");

		}
		m_Artifact = basicCegarLoop.getArtifact();
	}

	private void reportPositiveResults(Collection<ProgramPoint> errorLocs) {
		final String longDescription;
		if (errorLocs.isEmpty()) {
			longDescription = "We were not able to verify any"
					+ " specifiation because the program does not contain any specification.";
		} else {
			longDescription = errorLocs.size() + " specifications checked. All of them hold";
			for (ProgramPoint errorLoc : errorLocs) {
				PositiveResult<RcfgElement> pResult = new PositiveResult<RcfgElement>(Activator.s_PLUGIN_NAME,
						errorLoc, mServices.getBacktranslationService().getTranslatorSequence());
				reportResult(pResult);
			}
		}
		AllSpecificationsHoldResult result = new AllSpecificationsHoldResult(Activator.s_PLUGIN_NAME, longDescription);
		reportResult(result);
		// s_Logger.info(result.getShortDescription() + " " +
		// result.getLongDescription());
	}

	private void reportCounterexampleResult(RcfgProgramExecution pe) {
//		String ppls = ResultUtil.getPrettyprintedLocationSequence(pe);
//		mLogger.info(ppls);
		ProgramPoint errorPP = getErrorPP(pe);
		List<ILocation> failurePath = pe.getLocationList();
		ILocation origin = errorPP.getPayload().getLocation().getOrigin();

		List<ITranslator<?, ?, ?, ?>> translatorSequence = mServices.getBacktranslationService().getTranslatorSequence();
		if (pe.isOverapproximation()) {
			reportUnproveableResult(pe);
			return;
		}
		String ctxMessage = ResultUtil.getCheckedSpecification(errorPP).getNegativeMessage();
		ctxMessage += " (line " + origin.getStartLine() + ")";
		RCFGBacktranslator backtrans = (RCFGBacktranslator) translatorSequence.get(translatorSequence.size() - 1);
		BoogieProgramExecution bpe = (BoogieProgramExecution) backtrans.translateProgramExecution(pe);
		CounterExampleResult<RcfgElement, Expression> ctxRes = new CounterExampleResult<RcfgElement, Expression>(
				errorPP, Activator.s_PLUGIN_NAME, translatorSequence, pe,
				CounterExampleResult.getLocationSequence(bpe), bpe.getValuation(translatorSequence));
		ctxRes.setLongDescription(bpe.toString());
		reportResult(ctxRes);
		// s_Logger.warn(ctxMessage);
	}

	private void reportTimoutResult(Collection<ProgramPoint> errorLocs) {
		for (ProgramPoint errorLoc : errorLocs) {
			ILocation origin = errorLoc.getBoogieASTNode().getLocation().getOrigin();
			String timeOutMessage = "Unable to prove that "
					+ ResultUtil.getCheckedSpecification(errorLoc).getPositiveMessage();
			timeOutMessage += " (line " + origin.getStartLine() + ")";
			TimeoutResultAtElement<RcfgElement> timeOutRes = new TimeoutResultAtElement<RcfgElement>(errorLoc,
					Activator.s_PLUGIN_NAME, mServices.getBacktranslationService().getTranslatorSequence(), timeOutMessage);
			reportResult(timeOutRes);
			// s_Logger.warn(timeOutMessage);
		}
	}

	private void reportUnproveableResult(RcfgProgramExecution pe) {
		ProgramPoint errorPP = getErrorPP(pe);
		UnprovableResult<RcfgElement, RcfgElement, Expression> uknRes = new UnprovableResult<RcfgElement, RcfgElement, Expression>(
				Activator.s_PLUGIN_NAME, errorPP, mServices.getBacktranslationService().getTranslatorSequence(), pe);
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

	// Term simplify(Term term, RootNode rootNode) {
	// Script script = rootAnnot.getScript();
	// String unsimp = term.toStringDirect();
	// Term result = new SimplifyDDA(script, s_Logger).getSimplifiedTerm(term);
	// String simp = result.toStringDirect();
	// return result;
	// }

	private void reportResult(IResult res) {
		mServices.getResultService().reportResult(Activator.s_PLUGIN_ID, res);
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
		return ((HoareAnnotation) programPoint.getPayload().getAnnotations().get(Activator.s_PLUGIN_ID));
	}

	public ProgramPoint getErrorPP(RcfgProgramExecution rcfgProgramExecution) {
		int lastPosition = rcfgProgramExecution.getLength() - 1;
		CodeBlock last = rcfgProgramExecution.getTraceElement(lastPosition);
		ProgramPoint errorPP = (ProgramPoint) last.getTarget();
		return errorPP;
	}

}
