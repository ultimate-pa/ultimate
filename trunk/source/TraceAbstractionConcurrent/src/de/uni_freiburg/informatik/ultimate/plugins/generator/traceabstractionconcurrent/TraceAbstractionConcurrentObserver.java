package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Concurrency;
import de.uni_freiburg.informatik.ultimate.result.Check;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class TraceAbstractionConcurrentObserver implements IUnmanagedObserver {

	private final Logger mLogger;
	/**
	 * Root Node of this Ultimate model. I use this to store information that
	 * should be passed to the next plugin. The Successors of this node exactly
	 * the initial nodes of procedures.
	 */
	private static IElement m_graphroot = null;
	private final IUltimateServiceProvider mServices;

	public TraceAbstractionConcurrentObserver(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
	}

	@Override
	public boolean process(IElement root) {
		RootAnnot rootAnnot = ((RootNode) root).getRootAnnot();

		RootNode rootNode = (RootNode) root;
		TAPreferences taPrefs = new TAPreferences();

		mLogger.warn(taPrefs.dumpPath());

		SmtManager smtManager = new ConcurrentSmtManager(rootNode.getRootAnnot().getBoogie2SMT(), rootNode
				.getRootAnnot().getModGlobVarManager(), mServices);
		TraceAbstractionBenchmarks timingStatistics = new TraceAbstractionBenchmarks(rootNode.getRootAnnot());

		Map<String, Collection<ProgramPoint>> proc2errNodes = rootAnnot.getErrorNodes();
		Collection<ProgramPoint> errNodesOfAllProc = new ArrayList<ProgramPoint>();
		for (Collection<ProgramPoint> errNodeOfProc : proc2errNodes.values()) {
			errNodesOfAllProc.addAll(errNodeOfProc);
		}

		AbstractCegarLoop abstractCegarLoop;

		String name = "AllErrorsAtOnce";
		if (taPrefs.getConcurrency() == Concurrency.PETRI_NET) {
			abstractCegarLoop = new CegarLoopJulian(name, rootNode, smtManager, timingStatistics, taPrefs,
					errNodesOfAllProc, mServices);
		} else if (taPrefs.getConcurrency() == Concurrency.FINITE_AUTOMATA) {
			abstractCegarLoop = new CegarLoopConcurrentAutomata(name, rootNode, smtManager, timingStatistics, taPrefs,
					errNodesOfAllProc, mServices);
		} else {
			throw new IllegalArgumentException();
		}
		Result result = abstractCegarLoop.iterate();

		switch (result) {
		case SAFE:
			reportPositiveResult(errNodesOfAllProc);
			break;
		case UNSAFE: {
			RcfgProgramExecution pe = abstractCegarLoop.getRcfgProgramExecution();
			reportCounterexampleResult(pe);
			break;
		}
		case TIMEOUT:
			reportTimoutResult(errNodesOfAllProc);
			break;
		case UNKNOWN: {
			RcfgProgramExecution pe = abstractCegarLoop.getRcfgProgramExecution();
			reportUnproveableResult(pe);
		}
		}

		mLogger.info("Statistics - number of theorem prover calls: " + smtManager.getNontrivialSatQueries());
		mLogger.info("Statistics - iterations: " + abstractCegarLoop.getIteration());
		// s_Logger.info("Statistics - biggest abstraction: " +
		// abstractCegarLoop.m_BiggestAbstractionSize + " states");
		// s_Logger.info("Statistics - biggest abstraction in iteration: " +
		// abstractCegarLoop.m_BiggestAbstractionIteration);

		String stat = "";
		stat += "Statistics:  ";
		stat += " Iterations " + abstractCegarLoop.getIteration() + ".";
		stat += " CFG has ";
		stat += rootAnnot.getProgramPoints().size();
		stat += " locations,";
		stat += errNodesOfAllProc.size();
		stat += " error locations.";
		stat += " Satisfiability queries: ";
		stat += smtManager.getTrivialSatQueries() + " tivial, ";
		stat += smtManager.getNontrivialSatQueries() + " nontrivial.";
		// stat += " Biggest abstraction occured in iteration " +
		// abstractCegarLoop.m_BiggestAbstractionIteration + " had ";
		// stat += abstractCegarLoop.m_BiggestAbstractionSize;

		if (abstractCegarLoop instanceof CegarLoopJulian) {
			stat += " conditions ";
			CegarLoopJulian clj = (CegarLoopJulian) abstractCegarLoop;
			stat += "and " + clj.m_BiggestAbstractionTransitions + " transitions. ";
			stat += "Overall " + clj.m_CoRelationQueries + "co-relation queries";
		} else if (abstractCegarLoop instanceof CegarLoopConcurrentAutomata) {
			stat += " states ";
		} else {
			throw new IllegalArgumentException();
		}
		mLogger.warn(stat);
		mLogger.warn("PC#: " + smtManager.getInterpolQueries());
		mLogger.warn("TIME#: " + smtManager.getInterpolQuriesTime());
		mLogger.warn("EC#: " + smtManager.getNontrivialSatQueries());
		mLogger.warn("TIME#: " + smtManager.getSatCheckSolverTime());
		mLogger.warn("ManipulationTIME#: " + smtManager.getSatCheckTime());
		switch (result) {
		case SAFE:
			mLogger.warn("Program is correct");
			// FIXME This is not the right way to tell the core about results
			// ResultNotifier.programCorrect();
			break;
		case UNSAFE:
			mLogger.warn("Program is incorrect");
			// FIXME This is not the right way to tell the core about results
			// ResultNotifier.programIncorrect();
			break;
		case TIMEOUT:
			mLogger.warn("Insufficient iterations to proof correctness");
			// FIXME This is not the right way to tell the core about results
			// ResultNotifier
			// .programUnknown("Insufficient iterations to proof correctness");
			break;
		case UNKNOWN:
			mLogger.warn("Program might be incorrect, check conterexample.");
			// FIXME This is not the right way to tell the core about results
			// ResultNotifier.programUnknown("Program might be incorrect, check"
			// + " conterexample.");
			break;
		}

		m_graphroot = abstractCegarLoop.getArtifact();

		return false;
	}

	private void reportPositiveResult(Collection<ProgramPoint> errorPPs) {
		for (ProgramPoint errorPP : errorPPs) {
			PositiveResult<RcfgElement> pResult = new PositiveResult<RcfgElement>(Activator.s_PLUGIN_NAME, errorPP,
					mServices.getBacktranslationService());
			reportResult(pResult);
		}
	}

	private void reportCounterexampleResult(RcfgProgramExecution pe) {
		if (pe.isOverapproximation()) {
			reportUnproveableResult(pe);
			return;
		}
		reportResult(new CounterExampleResult<RcfgElement, CodeBlock, Expression>(getErrorPP(pe),
				Activator.s_PLUGIN_NAME, mServices.getBacktranslationService(), pe));
	}

	private void reportTimoutResult(Collection<ProgramPoint> errorLocs) {
		for (ProgramPoint errorLoc : errorLocs) {
			ILocation origin = errorLoc.getBoogieASTNode().getLocation().getOrigin();
			String timeOutMessage = "Timout! Unable to prove that "
					+ origin.checkedSpecification().getPositiveMessage();
			timeOutMessage += " (line " + origin.getStartLine() + ")";
			TimeoutResultAtElement<RcfgElement> timeOutRes = new TimeoutResultAtElement<RcfgElement>(errorLoc,
					Activator.s_PLUGIN_NAME, mServices.getBacktranslationService(), timeOutMessage);
			reportResult(timeOutRes);
			mLogger.warn(timeOutMessage);
		}
	}

	private void reportUnproveableResult(RcfgProgramExecution pe) {
		ProgramPoint errorPP = getErrorPP(pe);
		UnprovableResult<RcfgElement, CodeBlock, Expression> uknRes = new UnprovableResult<RcfgElement, CodeBlock, Expression>(
				Activator.s_PLUGIN_NAME, errorPP, mServices.getBacktranslationService(), pe);
		reportResult(uknRes);
	}

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

	public ProgramPoint getErrorPP(RcfgProgramExecution rcfgProgramExecution) {
		int lastPosition = rcfgProgramExecution.getLength() - 1;
		CodeBlock last = rcfgProgramExecution.getTraceElement(lastPosition).getTraceElement();
		ProgramPoint errorPP = (ProgramPoint) last.getTarget();
		return errorPP;
	}

}
