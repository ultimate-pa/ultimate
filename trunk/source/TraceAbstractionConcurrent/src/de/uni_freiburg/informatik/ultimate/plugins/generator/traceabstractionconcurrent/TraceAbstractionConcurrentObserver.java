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
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.IRunningTaskStackProvider;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgPetrifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgPetrifier.IcfgConstructionMode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgElement;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionStarter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionStarter.AllErrorsAtOnceDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Concurrency;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class TraceAbstractionConcurrentObserver implements IUnmanagedObserver {

	private final ILogger mLogger;
	/**
	 * Root Node of this Ultimate model. I use this to store information that should be passed to the next plugin. The
	 * Successors of this node exactly the initial nodes of procedures.
	 */
	private IElement mGraphroot = null;
	private final IUltimateServiceProvider mServices;

	public TraceAbstractionConcurrentObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public boolean process(final IElement root) {
		final IIcfg<? extends IcfgLocation> inputIcfg = (IIcfg) root;
		final IcfgPetrifier icfgPetrifier =
				new IcfgPetrifier(mServices, inputIcfg, IcfgConstructionMode.ASSUME_THREAD_INSTANCE_SUFFICIENCY);
		final IIcfg<? extends IcfgLocation> petrifiedIcfg = icfgPetrifier.getPetrifiedIcfg();
		mServices.getBacktranslationService().addTranslator(icfgPetrifier.getBacktranslator());
		final TAPreferences taPrefs = new TAPreferences(mServices);

		final CfgSmtToolkit csToolkit = petrifiedIcfg.getCfgSmtToolkit();
		final PredicateFactory predicateFactory = new PredicateFactory(mServices, csToolkit.getManagedScript(),
				csToolkit.getSymbolTable());
		final TraceAbstractionBenchmarks timingStatistics = new TraceAbstractionBenchmarks(petrifiedIcfg);
		final Set<IcfgLocation> threadErrorLocations;
		if (csToolkit.getConcurrencyInformation().getThreadInstanceMap().isEmpty()) {
			// no fork or join
			threadErrorLocations = Collections.emptySet();
		} else {
			threadErrorLocations = csToolkit.getConcurrencyInformation().getThreadInstanceMap().entrySet().stream()
					.map(x -> x.getValue().getErrorLocation()).collect(Collectors.toSet());
		}

		final Map<String, Set<? extends IcfgLocation>> proc2errNodes = (Map) petrifiedIcfg.getProcedureErrorNodes();
		final Collection<IcfgLocation> errNodesOfAllProc = new ArrayList<>();
		for (final Entry<String, Set<? extends IcfgLocation>> proc2errorLocs : proc2errNodes.entrySet()) {
			for (final IcfgLocation errorLoc : proc2errorLocs.getValue()) {
				if (!threadErrorLocations.contains(errorLoc)) {
					errNodesOfAllProc.add(errorLoc);
				}
			}
		}

		BasicCegarLoop<?> abstractCegarLoop;
		final AllErrorsAtOnceDebugIdentifier name = TraceAbstractionStarter.AllErrorsAtOnceDebugIdentifier.INSTANCE;
		if (taPrefs.getConcurrency() == Concurrency.PETRI_NET) {
			abstractCegarLoop = new CegarLoopJulian<>(name, petrifiedIcfg, csToolkit, predicateFactory,
					timingStatistics, taPrefs, errNodesOfAllProc, mServices);
		} else if (taPrefs.getConcurrency() == Concurrency.FINITE_AUTOMATA) {
			abstractCegarLoop = new CegarLoopConcurrentAutomata<>(name, petrifiedIcfg, csToolkit, predicateFactory,
					timingStatistics, taPrefs, errNodesOfAllProc, mServices);
		} else {
			throw new IllegalArgumentException();
		}
		final TraceAbstractionBenchmarks traceAbstractionBenchmark = new TraceAbstractionBenchmarks(petrifiedIcfg);
		final Result result = abstractCegarLoop.iterate();
		abstractCegarLoop.finish();
		final CegarLoopStatisticsGenerator cegarLoopBenchmarkGenerator = abstractCegarLoop.getCegarLoopBenchmark();
		cegarLoopBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.OverallTime.toString());
		traceAbstractionBenchmark.aggregateBenchmarkData(cegarLoopBenchmarkGenerator);
		reportBenchmark(traceAbstractionBenchmark);

		switch (result) {
		case SAFE:
			reportPositiveResults(errNodesOfAllProc);
			break;
		case UNSAFE:
			reportCounterexampleResult(abstractCegarLoop.getRcfgProgramExecution());
			break;
		case TIMEOUT:
		case USER_LIMIT_ITERATIONS:
		case USER_LIMIT_PATH_PROGRAM:
		case USER_LIMIT_TIME:
		case USER_LIMIT_TRACEHISTOGRAM:
			// TODO: The result handling is similar to that of the normal trace abstraction starter, merge the code and
			// use the logic from there. Until then, just threat user limits like timeouts
			reportTimeoutResult(result, errNodesOfAllProc, abstractCegarLoop.getRunningTaskStackProvider());
			break;
		case UNKNOWN:
			reportUnproveableResult(abstractCegarLoop.getRcfgProgramExecution(), null);
			break;
		default:
			throw new IllegalArgumentException();
		}

		mLogger.info("Statistics - iterations: " + abstractCegarLoop.getIteration());
		// s_Logger.info("Statistics - biggest abstraction: " +
		// abstractCegarLoop.mBiggestAbstractionSize + " states");
		// s_Logger.info("Statistics - biggest abstraction in iteration: " +
		// abstractCegarLoop.mBiggestAbstractionIteration);

		String stat = "";
		stat += "Statistics:  ";
		stat += " Iterations " + abstractCegarLoop.getIteration() + ".";
		stat += " CFG has ";
		stat += petrifiedIcfg.getProgramPoints().size();
		stat += " locations,";
		stat += errNodesOfAllProc.size();
		stat += " error locations.";
		stat += " Satisfiability queries: ";
		// stat += " Biggest abstraction occured in iteration " +
		// abstractCegarLoop.mBiggestAbstractionIteration + " had ";
		// stat += abstractCegarLoop.mBiggestAbstractionSize;

		if (abstractCegarLoop instanceof CegarLoopJulian) {
			stat += " conditions ";
			final CegarLoopJulian<?> clj = (CegarLoopJulian<?>) abstractCegarLoop;
			stat += "and " + clj.mBiggestAbstractionTransitions + " transitions. ";
			stat += "Overall " + clj.mCoRelationQueries + "co-relation queries";
		} else if (abstractCegarLoop instanceof CegarLoopConcurrentAutomata) {
			stat += " states ";
		} else {
			throw new IllegalArgumentException();
		}
		mLogger.warn(stat);
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
			// .programUnknown("Insufficient iterations to prove correctness");
			break;
		case UNKNOWN:
			mLogger.warn("Program might be incorrect, check conterexample.");
			// FIXME This is not the right way to tell the core about results
			// ResultNotifier.programUnknown("Program might be incorrect, check"
			// + " counterexample.");
			break;
		default:
			throw new IllegalArgumentException();
		}

		mGraphroot = abstractCegarLoop.getArtifact();

		return false;
	}

	private void reportPositiveResults(final Collection<? extends IcfgLocation> errorLocs) {
		if (!errorLocs.isEmpty()) {
			for (final IcfgLocation errorLoc : errorLocs) {
				final PositiveResult<IIcfgElement> pResult =
						new PositiveResult<>(Activator.PLUGIN_NAME, errorLoc, mServices.getBacktranslationService());
				reportResult(pResult);
			}
		}
		final AllSpecificationsHoldResult result =
				AllSpecificationsHoldResult.createAllSpecificationsHoldResult(Activator.PLUGIN_NAME, errorLocs.size());
		reportResult(result);
		mLogger.info(result.getShortDescription() + " " + result.getLongDescription());
	}

	private void reportCounterexampleResult(final IProgramExecution<IIcfgTransition<IcfgLocation>, Term> pe) {
		final List<UnprovabilityReason> upreasons = UnprovabilityReason.getUnprovabilityReasons(pe);
		if (!upreasons.isEmpty()) {
			reportUnproveableResult(pe, upreasons);
			return;
		}
		reportResult(new CounterExampleResult<>(getErrorPP(pe), Activator.PLUGIN_NAME,
				mServices.getBacktranslationService(), pe));
	}

	private void reportTimeoutResult(final Result result, final Collection<IcfgLocation> errorLocs,
			final IRunningTaskStackProvider rtsp) {
		for (final IcfgLocation errorIpp : errorLocs) {
			final IResult res = TraceAbstractionStarter.constructLimitResult(mServices, result, rtsp, errorIpp);
			reportResult(res);
		}
	}

	private void reportUnproveableResult(final IProgramExecution<IIcfgTransition<IcfgLocation>, Term> pe,
			final List<UnprovabilityReason> unproabilityReasons) {
		final IcfgLocation errorPP = getErrorPP(pe);
		reportResult(new UnprovableResult<>(Activator.PLUGIN_NAME, errorPP, mServices.getBacktranslationService(), pe,
				unproabilityReasons));
	}

	private <T> void reportBenchmark(final ICsvProviderProvider<T> benchmark) {
		final String shortDescription = "Ultimate Automizer benchmark data";
		final StatisticsResult<T> res = new StatisticsResult<>(Activator.PLUGIN_NAME, shortDescription, benchmark);
		reportResult(res);
	}

	private void reportResult(final IResult res) {
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, res);
	}

	/**
	 * @return the root of the CFG.
	 */
	public IElement getRoot() {
		return mGraphroot;
	}

	@Override
	public void finish() {
		// not needed
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		// not needed
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	public static IcfgLocation getErrorPP(final IProgramExecution<IIcfgTransition<IcfgLocation>, Term> pe) {
		final int lastPosition = pe.getLength() - 1;
		final IIcfgTransition<?> last = pe.getTraceElement(lastPosition).getTraceElement();
		final IcfgLocation errorPP = last.getTarget();
		return errorPP;
	}

}
