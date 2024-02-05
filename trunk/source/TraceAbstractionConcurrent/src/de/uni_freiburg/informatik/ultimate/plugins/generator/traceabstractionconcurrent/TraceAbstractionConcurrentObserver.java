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

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgPetrifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.petrinetlbe.IcfgCompositionFactory;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopResultReporter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionStarter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionStarter.AllErrorsAtOnceDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.CegarLoopForPetriNet;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Concurrency;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

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
		final IIcfg<? extends IcfgLocation> inputIcfg = (IIcfg<?>) root;
		final int numberOfThreadInstances = 3;
		final IcfgPetrifier icfgPetrifier = new IcfgPetrifier(mServices, inputIcfg, numberOfThreadInstances, false);
		final IIcfg<? extends IcfgLocation> petrifiedIcfg = icfgPetrifier.getPetrifiedIcfg();
		mServices.getBacktranslationService().addTranslator(icfgPetrifier.getBacktranslator());
		final TAPreferences taPrefs = new TAPreferences(mServices);

		final CfgSmtToolkit csToolkit = petrifiedIcfg.getCfgSmtToolkit();
		final PredicateFactory predicateFactory =
				new PredicateFactory(mServices, csToolkit.getManagedScript(), csToolkit.getSymbolTable());
		final TraceAbstractionBenchmarks timingStatistics = new TraceAbstractionBenchmarks(petrifiedIcfg);
		final Set<IcfgLocation> threadErrorLocations;
		if (IcfgUtils.isConcurrent(petrifiedIcfg)) {
			throw new UnsupportedOperationException();
		}
		// no fork or join
		threadErrorLocations = Collections.emptySet();

		final Map<String, Set<? extends IcfgLocation>> proc2errNodes = (Map) petrifiedIcfg.getProcedureErrorNodes();
		final Set<IcfgLocation> errNodesOfAllProc = new LinkedHashSet<>();
		for (final Entry<String, Set<? extends IcfgLocation>> proc2errorLocs : proc2errNodes.entrySet()) {
			for (final IcfgLocation errorLoc : proc2errorLocs.getValue()) {
				if (!threadErrorLocations.contains(errorLoc)) {
					errNodesOfAllProc.add(errorLoc);
				}
			}
		}

		BasicCegarLoop<IcfgEdge, ?, ?, ?> basicCegarLoop;
		final AllErrorsAtOnceDebugIdentifier name = TraceAbstractionStarter.AllErrorsAtOnceDebugIdentifier.INSTANCE;
		final PredicateFactoryRefinement stateFactoryForRefinement = new PredicateFactoryRefinement(mServices,
				csToolkit.getManagedScript(), predicateFactory, false, Collections.emptySet());

		if (taPrefs.getAutomataTypeConcurrency() == Concurrency.PETRI_NET) {
			final IcfgCompositionFactory compositionFactory = new IcfgCompositionFactory(mServices, csToolkit);
			basicCegarLoop = new CegarLoopForPetriNet<>(name,
					CegarLoopFactory.createPetriAbstraction(mServices, compositionFactory, predicateFactory,
							IcfgEdge.class, taPrefs, false, (IIcfg<IcfgLocation>) petrifiedIcfg, errNodesOfAllProc),
					petrifiedIcfg, csToolkit, predicateFactory, taPrefs, errNodesOfAllProc, mServices, IcfgEdge.class,
					stateFactoryForRefinement);
		} else if (taPrefs.getAutomataTypeConcurrency() == Concurrency.FINITE_AUTOMATA) {
			basicCegarLoop = new CegarLoopConcurrentAutomata<>(name, petrifiedIcfg, csToolkit, predicateFactory,
					taPrefs, errNodesOfAllProc, mServices, IcfgEdge.class, stateFactoryForRefinement);
		} else {
			throw new IllegalArgumentException();
		}
		final TraceAbstractionBenchmarks traceAbstractionBenchmark = new TraceAbstractionBenchmarks(petrifiedIcfg);
		final CegarLoopResult<IcfgEdge, ?> result = basicCegarLoop.runCegar();
		final IStatisticsDataProvider cegarLoopBenchmarkGenerator = basicCegarLoop.getCegarLoopBenchmark();
		traceAbstractionBenchmark.aggregateBenchmarkData(cegarLoopBenchmarkGenerator);
		reportBenchmark(traceAbstractionBenchmark);

		final CegarLoopResultReporter<IcfgEdge> clrReporter =
				new CegarLoopResultReporter<>(mServices, mLogger, Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
		clrReporter.reportCegarLoopResult(result);
		clrReporter.reportAllSafeResultIfNecessary(result, errNodesOfAllProc.size());

		// mLogger.info("Statistics - iterations: " + abstractCegarLoop.getIteration());
		// s_Logger.info("Statistics - biggest abstraction: " +
		// abstractCegarLoop.mBiggestAbstractionSize + " states");
		// s_Logger.info("Statistics - biggest abstraction in iteration: " +
		// abstractCegarLoop.mBiggestAbstractionIteration);

		String stat = "";
		stat += "Statistics:  ";
		// stat += " Iterations " + abstractCegarLoop.getIteration() + ".";
		stat += " CFG has ";
		stat += petrifiedIcfg.getProgramPoints().size();
		stat += " locations,";
		stat += errNodesOfAllProc.size();
		stat += " error locations.";
		stat += " Satisfiability queries: ";
		// stat += " Biggest abstraction occured in iteration " +
		// abstractCegarLoop.mBiggestAbstractionIteration + " had ";
		// stat += abstractCegarLoop.mBiggestAbstractionSize;

		if (basicCegarLoop instanceof CegarLoopForPetriNet) {
			stat += " conditions ";
			final CegarLoopForPetriNet<?> clj = (CegarLoopForPetriNet<?>) basicCegarLoop;
			stat += "and " + clj.mBiggestAbstractionTransitions + " transitions. ";
			stat += "Overall " + clj.mCoRelationQueries + "co-relation queries";
		} else if (basicCegarLoop instanceof CegarLoopConcurrentAutomata) {
			stat += " states ";
		} else {
			throw new IllegalArgumentException();
		}
		mLogger.warn(stat);

		mGraphroot = basicCegarLoop.getArtifact();

		return false;
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

	public static IcfgLocation getErrorPP(final IProgramExecution<IcfgEdge, Term> pe) {
		final int lastPosition = pe.getLength() - 1;
		final IIcfgTransition<?> last = pe.getTraceElement(lastPosition).getTraceElement();
		final IcfgLocation errorPP = last.getTarget();
		return errorPP;
	}

}
