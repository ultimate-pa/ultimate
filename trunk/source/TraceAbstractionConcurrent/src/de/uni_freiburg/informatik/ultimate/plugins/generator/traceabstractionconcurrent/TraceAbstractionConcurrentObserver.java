/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstractionConcurrent plug-in.
 * 
 * The ULTIMATE TraceAbstractionConcurrent plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstractionConcurrent plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstractionConcurrent plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstractionConcurrent plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstractionConcurrent plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.services.model.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.ModelType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopBenchmarkType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Concurrency;
import de.uni_freiburg.informatik.ultimate.result.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.result.Check;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.result.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.result.model.IResult;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;

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
	private IElement m_Graphroot = null;
	private final IUltimateServiceProvider m_Services;
	private final IToolchainStorage m_ToolchainStorage;

	public TraceAbstractionConcurrentObserver(IUltimateServiceProvider services, IToolchainStorage storage) {
		m_Services = services;
		m_ToolchainStorage = storage;
		mLogger = m_Services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
	}

	@Override
	public boolean process(IElement root) {
		RootAnnot rootAnnot = ((RootNode) root).getRootAnnot();

		RootNode rootNode = (RootNode) root;
		TAPreferences taPrefs = new TAPreferences();

		mLogger.warn(taPrefs.dumpPath());

		SmtManager smtManager = new SmtManager(rootNode.getRootAnnot().getBoogie2SMT().getScript(), rootNode.getRootAnnot().getBoogie2SMT(), rootNode
				.getRootAnnot().getModGlobVarManager(), m_Services, false, rootNode.getRootAnnot().getManagedScript());
		TraceAbstractionBenchmarks timingStatistics = new TraceAbstractionBenchmarks(rootNode.getRootAnnot());

		Map<String, Collection<ProgramPoint>> proc2errNodes = rootAnnot.getErrorNodes();
		Collection<ProgramPoint> errNodesOfAllProc = new ArrayList<ProgramPoint>();
		for (Collection<ProgramPoint> errNodeOfProc : proc2errNodes.values()) {
			errNodesOfAllProc.addAll(errNodeOfProc);
		}

		BasicCegarLoop abstractCegarLoop;

		String name = "AllErrorsAtOnce";
		if (taPrefs.getConcurrency() == Concurrency.PETRI_NET) {
			abstractCegarLoop = new CegarLoopJulian(name, rootNode, smtManager, timingStatistics, taPrefs,
					errNodesOfAllProc, m_Services, m_ToolchainStorage);
		} else if (taPrefs.getConcurrency() == Concurrency.FINITE_AUTOMATA) {
			abstractCegarLoop = new CegarLoopConcurrentAutomata(name, rootNode, smtManager, timingStatistics, taPrefs,
					errNodesOfAllProc, m_Services, m_ToolchainStorage);
		} else {
			throw new IllegalArgumentException();
		}
		TraceAbstractionBenchmarks traceAbstractionBenchmark = new TraceAbstractionBenchmarks(rootAnnot);
		Result result = abstractCegarLoop.iterate();
		abstractCegarLoop.finish();
		CegarLoopBenchmarkGenerator cegarLoopBenchmarkGenerator = abstractCegarLoop.getCegarLoopBenchmark();
		cegarLoopBenchmarkGenerator.stop(CegarLoopBenchmarkType.s_OverallTime);
		traceAbstractionBenchmark.aggregateBenchmarkData(cegarLoopBenchmarkGenerator);
		reportBenchmark(traceAbstractionBenchmark);

		switch (result) {
		case SAFE:
			reportPositiveResults(errNodesOfAllProc);
			break;
		case UNSAFE: {
			RcfgProgramExecution pe = abstractCegarLoop.getRcfgProgramExecution();
			reportCounterexampleResult(pe);
			break;
		}
		case TIMEOUT:
			reportTimeoutResult(errNodesOfAllProc);
			break;
		case UNKNOWN: {
			RcfgProgramExecution pe = abstractCegarLoop.getRcfgProgramExecution();
			reportUnproveableResult(pe, null);
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

		m_Graphroot = abstractCegarLoop.getArtifact();

		return false;
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
						errorLoc, m_Services.getBacktranslationService());
				reportResult(pResult);
			}
		}
		AllSpecificationsHoldResult result = new AllSpecificationsHoldResult(Activator.s_PLUGIN_NAME, longDescription);
		reportResult(result);
		mLogger.info(result.getShortDescription() + " " + result.getLongDescription());
	}

	private void reportCounterexampleResult(RcfgProgramExecution pe) {
		if (!pe.getOverapproximations().isEmpty()) {
			reportUnproveableResult(pe, pe.getUnprovabilityReasons());
			return;
		}
		reportResult(new CounterExampleResult<RcfgElement, RCFGEdge, Expression>(getErrorPP(pe),
				Activator.s_PLUGIN_NAME, m_Services.getBacktranslationService(), pe));
	}

	private void reportTimeoutResult(Collection<ProgramPoint> errorLocs) {
		for (ProgramPoint errorIpp : errorLocs) {
			ProgramPoint errorLoc = (ProgramPoint) errorIpp;
			ILocation origin = errorLoc.getBoogieASTNode().getLocation().getOrigin();
			String timeOutMessage = "Timeout! Unable to prove that "
					+ origin.getCheck().getPositiveMessage();
			timeOutMessage += " (line " + origin.getStartLine() + ")";
			TimeoutResultAtElement<RcfgElement> timeOutRes = new TimeoutResultAtElement<RcfgElement>(errorLoc,
					Activator.s_PLUGIN_NAME, m_Services.getBacktranslationService(), timeOutMessage);
			reportResult(timeOutRes);
			mLogger.warn(timeOutMessage);
		}
	}

	private void reportUnproveableResult(RcfgProgramExecution pe, List<UnprovabilityReason> unproabilityReasons) {
		ProgramPoint errorPP = getErrorPP(pe);
		UnprovableResult<RcfgElement, RCFGEdge, Expression> uknRes = new UnprovableResult<RcfgElement, RCFGEdge, Expression>(
				Activator.s_PLUGIN_NAME, errorPP, m_Services.getBacktranslationService(), pe, unproabilityReasons);
		reportResult(uknRes);
	}
	
	private <T> void reportBenchmark(ICsvProviderProvider<T> benchmark) {
		String shortDescription = "Ultimate Automizer benchmark data";
		BenchmarkResult<T> res = new BenchmarkResult<T>(Activator.s_PLUGIN_NAME, shortDescription, benchmark);
		// s_Logger.warn(res.getLongDescription());

		reportResult(res);
	}

	private void reportResult(IResult res) {
		m_Services.getResultService().reportResult(Activator.s_PLUGIN_ID, res);
	}

	/**
	 * @return the root of the CFG.
	 */
	public IElement getRoot() {
		return m_Graphroot;
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
	public void init(ModelType modelType, int currentModelIndex, int numberOfModels) {
		// TODO Auto-generated method stub

	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}

	public ProgramPoint getErrorPP(RcfgProgramExecution rcfgProgramExecution) {
		int lastPosition = rcfgProgramExecution.getLength() - 1;
		RCFGEdge last = rcfgProgramExecution.getTraceElement(lastPosition).getTraceElement();
		ProgramPoint errorPP = (ProgramPoint) last.getTarget();
		return errorPP;
	}

}
