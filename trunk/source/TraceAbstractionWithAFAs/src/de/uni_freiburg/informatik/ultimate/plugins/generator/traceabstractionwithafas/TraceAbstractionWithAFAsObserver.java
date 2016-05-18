/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstractionWithAFAs plug-in.
 * 
 * The ULTIMATE TraceAbstractionWithAFAs plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstractionWithAFAs plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstractionWithAFAs plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstractionWithAFAs plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstractionWithAFAs plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionwithafas;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultUtil;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class TraceAbstractionWithAFAsObserver extends BaseObserver {

	/**
	 * Root Node of this Ultimate model. I use this to store information that
	 * should be passed to the next plugin. The Successors of this node exactly
	 * the initial nodes of procedures.
	 */
	private IElement m_graphroot = null;

	private final IUltimateServiceProvider mServices;
	private final IToolchainStorage m_ToolchainStorage;

	private final ILogger mLogger;

	public TraceAbstractionWithAFAsObserver(IUltimateServiceProvider services, IToolchainStorage storage) {
		mServices = services;
		m_ToolchainStorage = storage;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
	}

	@Override
	public boolean process(IElement root) {

		RootNode rootNode = (RootNode) root;
		RootAnnot rootAnnot = rootNode.getRootAnnot();
		SmtManager smtManager = new SmtManager(rootAnnot.getScript(), rootAnnot.getBoogie2SMT(), rootAnnot.getModGlobVarManager(), mServices, false, rootAnnot.getManagedScript());
		TraceAbstractionBenchmarks taBenchmarks = new TraceAbstractionBenchmarks(rootAnnot);
		TAPreferences taPrefs = new TAPreferences();

		Map<String, Collection<ProgramPoint>> proc2errNodes = rootAnnot.getErrorNodes();
		Collection<ProgramPoint> errNodesOfAllProc = new ArrayList<ProgramPoint>();
		for (Collection<ProgramPoint> errNodeOfProc : proc2errNodes.values()) {
			errNodesOfAllProc.addAll(errNodeOfProc);
		}

		TAwAFAsCegarLoop cegarLoop = new TAwAFAsCegarLoop("bla", rootNode, smtManager, taBenchmarks, taPrefs,
				errNodesOfAllProc, taPrefs.interpolation(), taPrefs.computeHoareAnnotation(), mServices, m_ToolchainStorage);

		Result result = cegarLoop.iterate();
		
		cegarLoop.finish();

		TraceAbstractionBenchmarks taBenchmark = new TraceAbstractionBenchmarks(rootAnnot);
		CegarLoopStatisticsGenerator cegarLoopBenchmarkGenerator = cegarLoop.getCegarLoopBenchmark();
		cegarLoopBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.OverallTime.toString());
		taBenchmark.aggregateBenchmarkData(cegarLoopBenchmarkGenerator);
		reportBenchmark(taBenchmark);
	
		if (result == Result.SAFE) {
			reportPositiveResults(errNodesOfAllProc);
		} else if (result == Result.UNSAFE) {
			reportCounterexampleResult(cegarLoop.getRcfgProgramExecution());
		} else {
			String shortDescription = "Unable to decide if program is safe!";
			String longDescription = "Unable to decide if program is safe!";
			GenericResult genResult = new GenericResult(Activator.s_PLUGIN_NAME, shortDescription, longDescription,
					Severity.INFO);
			mServices.getResultService().reportResult(Activator.s_PLUGIN_ID, genResult);
		}
		return false;
	}
	
	
	private <T> void reportBenchmark(ICsvProviderProvider<T> benchmark) {
		String shortDescription = "Ultimate CodeCheck benchmark data";
		BenchmarkResult<T> res = new BenchmarkResult<T>(Activator.s_PLUGIN_NAME, shortDescription, benchmark);
		// s_Logger.warn(res.getLongDescription());

		reportResult(res);
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
						errorLoc, mServices.getBacktranslationService());
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

		reportResult(new CounterExampleResult<RcfgElement,RCFGEdge, Expression>(getErrorPP(pe), Activator.s_PLUGIN_NAME,
				mServices.getBacktranslationService(), pe));
	}

	private void reportUnproveableResult(RcfgProgramExecution pe, List<UnprovabilityReason> unproabilityReasons) {
		ProgramPoint errorPP = getErrorPP(pe);
		UnprovableResult<RcfgElement, RCFGEdge, Expression> uknRes = new UnprovableResult<RcfgElement, RCFGEdge, Expression>(
				Activator.s_PLUGIN_NAME, errorPP, mServices.getBacktranslationService(), pe, unproabilityReasons);
		reportResult(uknRes);
	}

	public ProgramPoint getErrorPP(RcfgProgramExecution rcfgProgramExecution) {
		int lastPosition = rcfgProgramExecution.getLength() - 1;
		RCFGEdge last = rcfgProgramExecution.getTraceElement(lastPosition).getTraceElement();
		ProgramPoint errorPP = (ProgramPoint) last.getTarget();
		return errorPP;
	}
	
	private void reportTimeoutResult(Collection<ProgramPoint> errorLocs) {
		for (ProgramPoint errorIpp : errorLocs) {
			ProgramPoint errorLoc = errorIpp;
			ILocation origin = errorLoc.getBoogieASTNode().getLocation().getOrigin();
			String timeOutMessage = "Unable to prove that "
					+ ResultUtil.getCheckedSpecification(errorLoc).getPositiveMessage();
			timeOutMessage += " (line " + origin.getStartLine() + ")";
			TimeoutResultAtElement<RcfgElement> timeOutRes = new TimeoutResultAtElement<RcfgElement>(errorLoc,
					Activator.s_PLUGIN_NAME, mServices.getBacktranslationService(),
					timeOutMessage);
			reportResult(timeOutRes);
		}
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

}
