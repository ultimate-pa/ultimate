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
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RcfgProgramExecution;
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
	private final IElement mgraphroot = null;

	private final IUltimateServiceProvider mServices;
	private final IToolchainStorage mToolchainStorage;

	private final ILogger mLogger;

	public TraceAbstractionWithAFAsObserver(final IUltimateServiceProvider services, final IToolchainStorage storage) {
		mServices = services;
		mToolchainStorage = storage;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
	}

	@Override
	public boolean process(final IElement root) {

		final RootNode rootNode = (RootNode) root;
		final RootAnnot rootAnnot = rootNode.getRootAnnot();
		final TAPreferences taPrefs = new TAPreferences(mServices);
		final SmtManager smtManager = new SmtManager(rootAnnot.getScript(), rootAnnot.getBoogie2SMT(), rootAnnot.getModGlobVarManager(), mServices, false, rootAnnot.getManagedScript(), taPrefs.getSimplificationTechnique(), taPrefs.getXnfConversionTechnique());
		final TraceAbstractionBenchmarks taBenchmarks = new TraceAbstractionBenchmarks(rootAnnot);
		

		final Map<String, Collection<ProgramPoint>> proc2errNodes = rootAnnot.getErrorNodes();
		final Collection<ProgramPoint> errNodesOfAllProc = new ArrayList<ProgramPoint>();
		for (final Collection<ProgramPoint> errNodeOfProc : proc2errNodes.values()) {
			errNodesOfAllProc.addAll(errNodeOfProc);
		}

		final TAwAFAsCegarLoop cegarLoop = new TAwAFAsCegarLoop("bla", rootNode, smtManager, taBenchmarks, taPrefs,
				errNodesOfAllProc, taPrefs.interpolation(), taPrefs.computeHoareAnnotation(), mServices, mToolchainStorage);

		final Result result = cegarLoop.iterate();
		
		cegarLoop.finish();

		final TraceAbstractionBenchmarks taBenchmark = new TraceAbstractionBenchmarks(rootAnnot);
		final CegarLoopStatisticsGenerator cegarLoopBenchmarkGenerator = cegarLoop.getCegarLoopBenchmark();
		cegarLoopBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.OverallTime.toString());
		taBenchmark.aggregateBenchmarkData(cegarLoopBenchmarkGenerator);
		reportBenchmark(taBenchmark);
	
		if (result == Result.SAFE) {
			reportPositiveResults(errNodesOfAllProc);
		} else if (result == Result.UNSAFE) {
			reportCounterexampleResult(cegarLoop.getRcfgProgramExecution());
		} else {
			final String shortDescription = "Unable to decide if program is safe!";
			final String longDescription = "Unable to decide if program is safe!";
			final GenericResult genResult = new GenericResult(Activator.s_PLUGIN_NAME, shortDescription, longDescription,
					Severity.INFO);
			mServices.getResultService().reportResult(Activator.s_PLUGIN_ID, genResult);
		}
		return false;
	}
	
	
	private <T> void reportBenchmark(final ICsvProviderProvider<T> benchmark) {
		final String shortDescription = "Ultimate CodeCheck benchmark data";
		final BenchmarkResult<T> res = new BenchmarkResult<T>(Activator.s_PLUGIN_NAME, shortDescription, benchmark);
		// s_Logger.warn(res.getLongDescription());

		reportResult(res);
	}

	private void reportPositiveResults(final Collection<ProgramPoint> errorLocs) {
		final String longDescription;
		if (errorLocs.isEmpty()) {
			longDescription = "We were not able to verify any"
					+ " specifiation because the program does not contain any specification.";
		} else {
			longDescription = errorLocs.size() + " specifications checked. All of them hold";
			for (final ProgramPoint errorLoc : errorLocs) {
				final PositiveResult<RcfgElement> pResult = new PositiveResult<RcfgElement>(Activator.s_PLUGIN_NAME,
						errorLoc, mServices.getBacktranslationService());
				reportResult(pResult);
			}
		}
		final AllSpecificationsHoldResult result = new AllSpecificationsHoldResult(Activator.s_PLUGIN_NAME, longDescription);
		reportResult(result);
		mLogger.info(result.getShortDescription() + " " + result.getLongDescription());
	}

	private void reportCounterexampleResult(final RcfgProgramExecution pe) {
		if (!pe.getOverapproximations().isEmpty()) {
			reportUnproveableResult(pe, pe.getUnprovabilityReasons());
			return;
		}

		reportResult(new CounterExampleResult<RcfgElement,RCFGEdge, Term>(getErrorPP(pe), Activator.s_PLUGIN_NAME,
				mServices.getBacktranslationService(), pe));
	}

	private void reportUnproveableResult(final RcfgProgramExecution pe, final List<UnprovabilityReason> unproabilityReasons) {
		final ProgramPoint errorPP = getErrorPP(pe);
		final UnprovableResult<RcfgElement, RCFGEdge, Term> uknRes = new UnprovableResult<RcfgElement, RCFGEdge, Term>(
				Activator.s_PLUGIN_NAME, errorPP, mServices.getBacktranslationService(), pe, unproabilityReasons);
		reportResult(uknRes);
	}

	public ProgramPoint getErrorPP(final RcfgProgramExecution rcfgProgramExecution) {
		final int lastPosition = rcfgProgramExecution.getLength() - 1;
		final RCFGEdge last = rcfgProgramExecution.getTraceElement(lastPosition).getTraceElement();
		final ProgramPoint errorPP = (ProgramPoint) last.getTarget();
		return errorPP;
	}
	
	private void reportTimeoutResult(final Collection<ProgramPoint> errorLocs) {
		for (final ProgramPoint errorIpp : errorLocs) {
			final ProgramPoint errorLoc = errorIpp;
			final ILocation origin = errorLoc.getBoogieASTNode().getLocation().getOrigin();
			String timeOutMessage = "Unable to prove that "
					+ ResultUtil.getCheckedSpecification(errorLoc).getPositiveMessage();
			timeOutMessage += " (line " + origin.getStartLine() + ")";
			final TimeoutResultAtElement<RcfgElement> timeOutRes = new TimeoutResultAtElement<RcfgElement>(errorLoc,
					Activator.s_PLUGIN_NAME, mServices.getBacktranslationService(),
					timeOutMessage);
			reportResult(timeOutRes);
		}
	}

	private void reportResult(final IResult res) {
		mServices.getResultService().reportResult(Activator.s_PLUGIN_ID, res);
	}

	/**
	 * @return the root of the CFG.
	 */
	public IElement getRoot() {
		return mgraphroot;
	}

}
