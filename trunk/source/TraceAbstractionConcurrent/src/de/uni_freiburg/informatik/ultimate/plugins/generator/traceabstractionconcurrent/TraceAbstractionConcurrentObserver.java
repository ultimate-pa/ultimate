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
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultUtil;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgElement;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
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
	private final IToolchainStorage mToolchainStorage;

	public TraceAbstractionConcurrentObserver(final IUltimateServiceProvider services,
			final IToolchainStorage storage) {
		mServices = services;
		mToolchainStorage = storage;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public boolean process(final IElement root) {
		final BoogieIcfgContainer rootAnnot = (BoogieIcfgContainer) root;

		final BoogieIcfgContainer rootNode = (BoogieIcfgContainer) root;
		final TAPreferences taPrefs = new TAPreferences(mServices);

		mLogger.warn(taPrefs.dumpPath());

		final CfgSmtToolkit csToolkit = rootAnnot.getCfgSmtToolkit();
		final PredicateFactory predicateFactory = new PredicateFactory(mServices, csToolkit.getManagedScript(),
				csToolkit.getSymbolTable(), taPrefs.getSimplificationTechnique(), taPrefs.getXnfConversionTechnique());
		final TraceAbstractionBenchmarks timingStatistics = new TraceAbstractionBenchmarks(rootNode);

		final Map<String, Set<BoogieIcfgLocation>> proc2errNodes = rootAnnot.getProcedureErrorNodes();
		final Collection<BoogieIcfgLocation> errNodesOfAllProc = new ArrayList<>();
		for (final Collection<BoogieIcfgLocation> errNodeOfProc : proc2errNodes.values()) {
			errNodesOfAllProc.addAll(errNodeOfProc);
		}

		BasicCegarLoop<?> abstractCegarLoop;

		final String name = "AllErrorsAtOnce";
		if (taPrefs.getConcurrency() == Concurrency.PETRI_NET) {
			abstractCegarLoop = new CegarLoopJulian<>(name, rootNode, csToolkit, predicateFactory, timingStatistics,
					taPrefs, errNodesOfAllProc, mServices, mToolchainStorage);
		} else if (taPrefs.getConcurrency() == Concurrency.FINITE_AUTOMATA) {
			abstractCegarLoop = new CegarLoopConcurrentAutomata<>(name, rootNode, csToolkit, predicateFactory,
					timingStatistics, taPrefs, errNodesOfAllProc, mServices, mToolchainStorage);
		} else {
			throw new IllegalArgumentException();
		}
		final TraceAbstractionBenchmarks traceAbstractionBenchmark = new TraceAbstractionBenchmarks(rootAnnot);
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
			reportTimeoutResult(errNodesOfAllProc);
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
		stat += rootAnnot.getProgramPoints().size();
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

	private void reportPositiveResults(final Collection<BoogieIcfgLocation> errorLocs) {
		if (!errorLocs.isEmpty()) {
			for (final BoogieIcfgLocation errorLoc : errorLocs) {
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

	private void reportCounterexampleResult(final IcfgProgramExecution pe) {
		if (!pe.getOverapproximations().isEmpty()) {
			reportUnproveableResult(pe, pe.getUnprovabilityReasons());
			return;
		}
		reportResult(new CounterExampleResult<>(getErrorPP(pe), Activator.PLUGIN_NAME,
				mServices.getBacktranslationService(), pe));
	}

	private void reportTimeoutResult(final Collection<BoogieIcfgLocation> errorLocs) {
		for (final BoogieIcfgLocation errorIpp : errorLocs) {
			final BoogieIcfgLocation errorLoc = errorIpp;
			final ILocation origin = errorLoc.getBoogieASTNode().getLocation();
			final Check check = ResultUtil.getCheckedSpecification(errorLoc.getBoogieASTNode());
			String timeOutMessage = "Timeout! Unable to prove that " + check.getPositiveMessage();
			timeOutMessage += " (line " + origin.getStartLine() + ")";
			final TimeoutResultAtElement<IIcfgElement> timeOutRes = new TimeoutResultAtElement<>(errorLoc,
					Activator.PLUGIN_NAME, mServices.getBacktranslationService(), timeOutMessage);
			reportResult(timeOutRes);
			mLogger.warn(timeOutMessage);
		}
	}

	private void reportUnproveableResult(final IcfgProgramExecution pe,
			final List<UnprovabilityReason> unproabilityReasons) {
		final IcfgLocation errorPP = getErrorPP(pe);
		reportResult(new UnprovableResult<>(Activator.PLUGIN_NAME, errorPP, mServices.getBacktranslationService(), pe,
				unproabilityReasons));
	}

	private <T> void reportBenchmark(final ICsvProviderProvider<T> benchmark) {
		final String shortDescription = "Ultimate Automizer benchmark data";
		final StatisticsResult<T> res = new StatisticsResult<>(Activator.PLUGIN_NAME, shortDescription, benchmark);
		// s_Logger.warn(res.getLongDescription());

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

	public static IcfgLocation getErrorPP(final IcfgProgramExecution rcfgProgramExecution) {
		final int lastPosition = rcfgProgramExecution.getLength() - 1;
		final IIcfgTransition<?> last = rcfgProgramExecution.getTraceElement(lastPosition).getTraceElement();
		final IcfgLocation errorPP = last.getTarget();
		return errorPP;
	}

}
