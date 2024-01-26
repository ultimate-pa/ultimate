/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessInvariant;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessProcedureContract;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.InvariantResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ProcedureContractResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultUtil;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Spec;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgPetrifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgElement;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.ProcedureErrorDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.ProcedureErrorDebugIdentifier.ProcedureErrorType;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.StringDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.BlockEncodingBacktranslator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.HoareAnnotation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.ICopyActionFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.HoareAnnotationChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.FloydHoareAutomataReuse;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.OrderOfErrorLocations;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

public class TraceAbstractionStarter<L extends IIcfgTransition<?>> {
	public enum CegarRestartBehaviour {
		ONLY_ONE_CEGAR, ONE_CEGAR_PER_THREAD_INSTANCE, ONE_CEGAR_PER_ERROR_LOCATION,
	}

	public static final String ULTIMATE_INIT = "ULTIMATE.init";
	public static final String ULTIMATE_START = "ULTIMATE.start";

	private static final long MILLISECONDS_PER_SECOND = 1000L;

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final TAPreferences mPrefs;
	private final boolean mComputeHoareAnnotation;
	private final boolean mIsConcurrent;
	private final INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> mWitnessAutomaton;
	private final CegarLoopFactory<L> mCegarFactory;

	/**
	 * Root Node of this Ultimate model. I use this to store information that should be passed to the next plugin. The
	 * Successors of this node exactly the initial nodes of procedures.
	 */
	private IElement mRootOfNewModel;
	private IElement mArtifact;

	private final List<INestedWordAutomaton<String, String>> mRawFloydHoareAutomataFromFile;
	private final List<Pair<AbstractInterpolantAutomaton<L>, IPredicateUnifier>> mFloydHoareAutomataFromErrorLocations =
			new ArrayList<>();

	// list has one entry per analysis restart with increased number of threads (only 1 entry if sequential)
	private final Map<DebugIdentifier, List<TraceAbstractionBenchmarks>> mStatistics = new LinkedHashMap<>();

	private Map<IcfgLocation, IcfgLocation> mLocationMap;
	private final Map<IcfgLocation, IResult> mResultsPerLocation;
	private final CegarLoopResultReporter<L> mResultReporter;

	public TraceAbstractionStarter(final IUltimateServiceProvider services, final IIcfg<IcfgLocation> icfg,
			final INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> witnessAutomaton,
			final List<INestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile,
			final Supplier<IPLBECompositionFactory<L>> createCompositionFactory,
			final ICopyActionFactory<L> copyFactory, final Class<L> transitionClazz) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mPrefs = new TAPreferences(mServices);
		mResultsPerLocation = new LinkedHashMap<>();
		mWitnessAutomaton = witnessAutomaton;
		mRawFloydHoareAutomataFromFile = rawFloydHoareAutomataFromFile;
		mIsConcurrent = IcfgUtils.isConcurrent(icfg);
		mResultReporter = new CegarLoopResultReporter<>(mServices, mLogger, Activator.PLUGIN_ID, Activator.PLUGIN_NAME,
				this::recordLocationResult);

		if (mPrefs.computeHoareAnnotation() && mIsConcurrent) {
			mLogger.warn("Switching off computation of Hoare annotation because input is a concurrent program");
			mComputeHoareAnnotation = false;
		} else {
			mComputeHoareAnnotation = mPrefs.computeHoareAnnotation();
		}

		mCegarFactory = new CegarLoopFactory<>(transitionClazz, mPrefs, createCompositionFactory, copyFactory,
				mComputeHoareAnnotation);

		runCegarLoops(icfg);
	}

	private void runCegarLoops(final IIcfg<IcfgLocation> icfg) {
		logSettings();

		final Collection<IcfgLocation> errNodesOfAllProc = IcfgUtils.getErrorLocations(icfg);
		final int numberOfErrorLocs = errNodesOfAllProc.size();
		mLogger.info("Applying trace abstraction to program that has " + numberOfErrorLocs + " error locations.");
		if (numberOfErrorLocs <= 0) {
			final AllSpecificationsHoldResult result = AllSpecificationsHoldResult
					.createAllSpecificationsHoldResult(Activator.PLUGIN_NAME, numberOfErrorLocs);
			mResultReporter.reportResult(result);
			return;
		}

		mArtifact = null;
		final List<CegarLoopResult<L>> results;
		if (IcfgUtils.isConcurrent(icfg)) {
			results = analyseConcurrentProgram(icfg);
		} else {
			results = analyseSequentialProgram(icfg);
		}

		mLogger.info("Computing trace abstraction results");
		// Report results that were buffered because they may be overridden or amended.
		reportLocationResults();
		reportBenchmarkResults();

		logNumberOfWitnessInvariants(errNodesOfAllProc);
		mResultReporter.reportAllSafeResultIfNecessary(results, numberOfErrorLocs);

		final IProgressMonitorService progmon = mServices.getProgressMonitorService();

		if (mComputeHoareAnnotation && progmon.continueProcessing() && results.stream().allMatch(
				a -> a.resultStream().allMatch(r -> r != Result.TIMEOUT && !Result.USER_LIMIT_RESULTS.contains(r)))) {
			final IBacktranslationService backTranslatorService = mServices.getBacktranslationService();
			createInvariantResults(icfg, backTranslatorService);
			createProcedureContractResults(icfg, backTranslatorService);
		}
		mRootOfNewModel = mArtifact;
	}

	private void logSettings() {
		String settings = "Automizer settings:";
		settings += " Hoare:" + mComputeHoareAnnotation;
		settings += " " + (mPrefs.differenceSenwa() ? "SeNWA" : "NWA");
		settings += " Interpolation:" + mPrefs.interpolation();
		settings += " Determinization: " + mPrefs.interpolantAutomatonEnhancement();
		mLogger.info(settings);
	}

	/**
	 * Analyses a concurrent program and detects if thread instances are insufficient. If so, the number of thread
	 * instances is increased and the analysis restarts.
	 *
	 * @param icfg
	 *            The CFG for the program (unpetrified).
	 * @return
	 */
	private List<CegarLoopResult<L>> analyseConcurrentProgram(final IIcfg<IcfgLocation> icfg) {
		if (icfg.getInitialNodes().size() > 1) {
			throw new UnsupportedOperationException("Library mode is not supported for concurrent programs. "
					+ "There must be a unique entry procedure.");
		}

		int numberOfThreadInstances = 1;
		while (true) {
			final IIcfg<IcfgLocation> petrifiedIcfg = petrify(icfg, numberOfThreadInstances);
			mResultsPerLocation.clear();

			final var results = analyseProgram(petrifiedIcfg, TraceAbstractionStarter::hasSufficientThreadInstances);
			// Stop if either every in-use error location is unreachable or any other error locations is reachable
			if (resultsHaveSufficientInstances(results)) {
				mLogger.info("Analysis of concurrent program completed with " + numberOfThreadInstances
						+ " thread instances");
				return results;
			}
			assert IcfgUtils.isConcurrent(icfg) : "Insufficient thread instances for sequential program";
			mLogger.warn(numberOfThreadInstances
					+ " thread instances were not sufficient, I will increase this number and restart the analysis");
			numberOfThreadInstances++;
		}
	}

	private static <L extends IIcfgTransition<?>> boolean
			resultsHaveSufficientInstances(final List<CegarLoopResult<L>> results) {
		boolean res = true;
		for (final CegarLoopResult<L> r : results) {
			if (r.resultStream().allMatch(a -> a != Result.UNSAFE)) {
				continue;
			}
			if (hasSufficientThreadInstances(r)) {
				return true;
			}
			res = false;
		}
		return res;
	}

	/**
	 * Analyses a sequential program (no special handling for threads is needed).
	 *
	 * @param icfg
	 *            The CFG for the program
	 * @return
	 */
	private List<CegarLoopResult<L>> analyseSequentialProgram(final IIcfg<IcfgLocation> icfg) {
		return analyseProgram(icfg, x -> true);
	}

	/**
	 * Helper method that runs one or more CEGAR loops (depending on settings, e.g. all at once or per assertion) to
	 * analyse a program. Results from all analyses are collected and returned.
	 *
	 * @param icfg
	 *            The CFG for the program
	 * @param continueAnalysis
	 *            A predicate that returns false if the analysis should be interrupted (and the results so far should be
	 *            returned).
	 * @return the collection of all analysis results, in order
	 */
	private List<CegarLoopResult<L>> analyseProgram(final IIcfg<IcfgLocation> icfg,
			final Predicate<CegarLoopResult<L>> continueAnalysis) {
		final List<CegarLoopResult<L>> results = new ArrayList<>();

		final List<Pair<DebugIdentifier, Set<IcfgLocation>>> errorPartitions = partitionErrorLocations(icfg);
		final boolean multiplePartitions = errorPartitions.size() > 1;

		final IProgressMonitorService progmon = mServices.getProgressMonitorService();
		int finishedErrorSets = 0;
		for (final Pair<DebugIdentifier, Set<IcfgLocation>> partition : errorPartitions) {
			final DebugIdentifier name = partition.getKey();
			final Set<IcfgLocation> errorLocs = partition.getValue();

			final IUltimateServiceProvider services;
			if (mPrefs.hasErrorLocTimeLimit()) {
				services = progmon.registerChildTimer(mServices,
						progmon.getTimer(mPrefs.getErrorLocTimeLimit() * MILLISECONDS_PER_SECOND * errorLocs.size()));
			} else {
				services = mServices;
			}
			if (multiplePartitions) {
				services.getProgressMonitorService().setSubtask(name.toString());
			}
			final TraceAbstractionBenchmarks traceAbstractionBenchmark = createNewBenchmark(name, icfg);

			final CegarLoopResult<L> clres =
					executeCegarLoop(services, name, icfg, traceAbstractionBenchmark, errorLocs);
			results.add(clres);
			finishedErrorSets++;

			if (multiplePartitions) {
				mLogger.info(String.format("Result for error location %s was %s (%s/%s)", name,
						clres.resultStream().map(Result::toString).collect(Collectors.joining(",")), finishedErrorSets,
						errorPartitions.size()));
			}
			if (!continueAnalysis.test(clres)) {
				break;
			}

			if (mPrefs.getFloydHoareAutomataReuse() != FloydHoareAutomataReuse.NONE) {
				mFloydHoareAutomataFromErrorLocations.addAll(clres.getFloydHoareAutomata());
			}
			mResultReporter.reportCegarLoopResult(clres);
			mArtifact = clres.getArtifact();

			if (mPrefs.stopAfterFirstViolation() && clres.resultStream().anyMatch(a -> a == Result.UNSAFE)) {
				// TODO: Report for all remaining errorLocs an unknown result
				break;
			}
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				// TODO: Report for all remaining errorLocs a timeout result
				break;
			}
		}

		return results;
	}

	/**
	 * Partitions the error locations of a CFG. Each partition shall be analysed separately, in the order in which they
	 * are returned.
	 *
	 * Currently, 2 modes are supported: all error locations at once, or each error location separately. In the future,
	 * other modes might be added.
	 *
	 * Don't forget to update {@link #getBenchmarkDescription(DebugIdentifier)} if more modes are implemented!
	 *
	 * @param icfg
	 *            The CFG whose error locations shall be partitioned.
	 * @return A partition of the error locations, each set annotated with a debug identifier
	 */
	private List<Pair<DebugIdentifier, Set<IcfgLocation>>> partitionErrorLocations(final IIcfg<IcfgLocation> icfg) {
		// TODO (Dominik 2021-04-29) Support other mode: group by original (i.e. all copies of a location together)

		CegarRestartBehaviour restartBehaviour = mServices.getPreferenceProvider(Activator.PLUGIN_ID).getEnum(
				TraceAbstractionPreferenceInitializer.LABEL_CEGAR_RESTART_BEHAVIOUR, CegarRestartBehaviour.class);
		if (restartBehaviour == CegarRestartBehaviour.ONE_CEGAR_PER_THREAD_INSTANCE && !mIsConcurrent) {
			mLogger.warn("Program is not concurrent. Changing CEGAR restart behaviour to "
					+ CegarRestartBehaviour.ONLY_ONE_CEGAR);
			restartBehaviour = CegarRestartBehaviour.ONLY_ONE_CEGAR;
		}

		if (restartBehaviour == CegarRestartBehaviour.ONE_CEGAR_PER_THREAD_INSTANCE) {
			assert mIsConcurrent : "One CEGAR per thread instance only works for concurrent programs";
			final List<Pair<DebugIdentifier, Set<IcfgLocation>>> result = new ArrayList<>();
			for (final String thread : IcfgUtils.getAllThreadInstances(icfg)) {
				final Set<IcfgLocation> locs = icfg.getProcedureErrorNodes().get(thread);
				if (!locs.isEmpty()) {
					final DebugIdentifier ident = new ThreadInstanceDebugIdentifier(thread);
					result.add(new Pair<>(ident, locs));
				}
			}
			return result;
		}

		final Set<IcfgLocation> errNodesOfAllProc = IcfgUtils.getErrorLocations(icfg);
		if (restartBehaviour == CegarRestartBehaviour.ONE_CEGAR_PER_ERROR_LOCATION) {
			Stream<IcfgLocation> errorLocs = errNodesOfAllProc.stream();
			if (mIsConcurrent && mPrefs.getOrderOfErrorLocations() == OrderOfErrorLocations.PROGRAM_FIRST) {
				switch (mPrefs.getOrderOfErrorLocations()) {
				case PROGRAM_FIRST:
					// Sort the errorLocs by their type, i.e. isInsufficientThreadsLocations last
					errorLocs = errorLocs.sorted((x, y) -> Boolean.compare(isInsufficientThreadsLocation(x),
							isInsufficientThreadsLocation(y)));
					break;
				case INSUFFICIENT_FIRST:
					// Sort the errorLocs by their type, i.e. isInsufficientThreadsLocations first
					errorLocs = errorLocs.sorted((x, y) -> Boolean.compare(isInsufficientThreadsLocation(y),
							isInsufficientThreadsLocation(x)));
					break;
				default:
					break;
				}
			}
			return errorLocs.map(x -> new Pair<>(x.getDebugIdentifier(), Set.of(x))).collect(Collectors.toList());
		}

		assert restartBehaviour == CegarRestartBehaviour.ONLY_ONE_CEGAR : "unsupported CEGAR restart behaviour";
		if (mIsConcurrent && mPrefs.getOrderOfErrorLocations() != OrderOfErrorLocations.TOGETHER
				&& !IcfgUtils.getForksInLoop(icfg).isEmpty()) {
			final Set<IcfgLocation> inUseErrors = new HashSet<>(getInUseErrorNodeMap(icfg).values());
			final Set<IcfgLocation> otherErrors = DataStructureUtils.difference(errNodesOfAllProc, inUseErrors);
			final Pair<DebugIdentifier, Set<IcfgLocation>> other =
					new Pair<>(AllErrorsAtOnceDebugIdentifier.INSTANCE, otherErrors);
			final Pair<DebugIdentifier, Set<IcfgLocation>> inUse =
					new Pair<>(InUseDebugIdentifier.INSTANCE, inUseErrors);
			if (mPrefs.getOrderOfErrorLocations() == OrderOfErrorLocations.INSUFFICIENT_FIRST) {
				return List.of(inUse, other);
			}
			return List.of(other, inUse);
		}
		return List.of(new Pair<>(AllErrorsAtOnceDebugIdentifier.INSTANCE, errNodesOfAllProc));
	}

	private CegarLoopResult<L> executeCegarLoop(final IUltimateServiceProvider services, final DebugIdentifier name,
			final IIcfg<IcfgLocation> icfg, final TraceAbstractionBenchmarks taBenchmark,
			final Set<IcfgLocation> errorLocs) {
		final CegarLoopResult<L> clres = mCegarFactory
				.constructCegarLoop(services, name, icfg, errorLocs, mWitnessAutomaton, mRawFloydHoareAutomataFromFile)
				.runCegar();

		final StatisticsData cegarStatistics = new StatisticsData();
		cegarStatistics.aggregateBenchmarkData(clres.getCegarLoopStatisticsGenerator());
		if (clres.getCegarLoopStatisticsGenerator().getBenchmarkType() instanceof PetriCegarStatisticsType) {
			cegarStatistics
					.aggregateBenchmarkData(new PetriCegarLoopStatisticsGenerator(mCegarFactory.getStatistics()));
		} else {
			cegarStatistics.aggregateBenchmarkData(mCegarFactory.getStatistics());
		}
		taBenchmark.aggregateBenchmarkData(cegarStatistics);
		return clres;
	}

	private static Map<IIcfgForkTransitionThreadCurrent<IcfgLocation>, IcfgLocation>
			getInUseErrorNodeMap(final IIcfg<?> icfg) {
		return icfg.getCfgSmtToolkit().getConcurrencyInformation().getInUseErrorNodeMap();
	}

	private void createInvariantResults(final IIcfg<IcfgLocation> icfg,
			final IBacktranslationService backTranslatorService) {
		final CfgSmtToolkit csToolkit = icfg.getCfgSmtToolkit();
		assert new HoareAnnotationChecker(mServices, icfg, csToolkit).isInductive() : "incorrect Hoare annotation";

		final Term trueterm = csToolkit.getManagedScript().getScript().term("true");

		final Set<IcfgLocation> locsForLoopLocations = new HashSet<>();

		locsForLoopLocations.addAll(IcfgUtils.getPotentialCycleProgramPoints(icfg));
		locsForLoopLocations.addAll(icfg.getLoopLocations());
		// find all locations that have outgoing edges which are annotated with LoopEntry, i.e., all loop candidates

		for (final IcfgLocation locNode : locsForLoopLocations) {
			final HoareAnnotation hoare = HoareAnnotation.getAnnotation(locNode);
			if (hoare == null) {
				continue;
			}
			final Term formula = hoare.getFormula();
			final InvariantResult<IIcfgElement, Term> invResult =
					new InvariantResult<>(Activator.PLUGIN_NAME, locNode, backTranslatorService, formula);
			mResultReporter.reportResult(invResult);

			if (formula.equals(trueterm)) {
				continue;
			}
			new WitnessInvariant(invResult.getInvariant()).annotate(locNode);
		}
	}

	private void createProcedureContractResults(final IIcfg<IcfgLocation> icfg,
			final IBacktranslationService backTranslatorService) {
		final Map<String, IcfgLocation> exitNodes = icfg.getProcedureExitNodes();
		final Map<String, IcfgLocation> entryNodes = icfg.getProcedureEntryNodes();
		for (final String procName : icfg.getProcedureEntryNodes().keySet()) {
			if (isAuxilliaryProcedure(procName)) {
				continue;
			}
			final IcfgLocation entry = entryNodes.get(procName);
			final IcfgLocation exit = exitNodes.get(procName);
			final HoareAnnotation ensures = HoareAnnotation.getAnnotation(exit);
			final HoareAnnotation requires = HoareAnnotation.getAnnotation(entry);
			if (ensures != null) {
				final Term ensuresFormula = ensures.getFormula();
				final Term requiresFormula = PredicateUtils.eliminateOldVars(mServices,
						icfg.getCfgSmtToolkit().getManagedScript(), requires);
				final ProcedureContractResult<IIcfgElement, Term> result = new ProcedureContractResult<>(
						Activator.PLUGIN_NAME, exit, backTranslatorService, procName, requiresFormula, ensuresFormula);
				mResultReporter.reportResult(result);
				new WitnessProcedureContract(result.getReqiresResult(), result.getEnsuresResult()).annotate(exit);
			}
		}
	}

	private void logNumberOfWitnessInvariants(final Collection<IcfgLocation> errNodesOfAllProc) {
		int numberOfCheckedInvariants = 0;
		for (final IcfgLocation err : errNodesOfAllProc) {
			if (!(err instanceof BoogieIcfgLocation)) {
				mLogger.info("Did not count any witness invariants because Icfg is not BoogieIcfg");
				return;
			}
			final BoogieASTNode boogieASTNode = ((BoogieIcfgLocation) err).getBoogieASTNode();
			final Check check = Check.getAnnotation(boogieASTNode);
			if (check != null && check.getSpec().contains(Spec.WITNESS_INVARIANT)) {
				numberOfCheckedInvariants++;
			}
		}
		if (numberOfCheckedInvariants > 0) {
			mLogger.info("Automizer considered " + numberOfCheckedInvariants + " witness invariants");
			mLogger.info("WitnessConsidered=" + numberOfCheckedInvariants);
		}
	}

	private static boolean isInsufficientThreadsIdentifier(final DebugIdentifier ident) {
		if (ident instanceof ProcedureErrorDebugIdentifier) {
			return ((ProcedureErrorDebugIdentifier) ident).getType() == ProcedureErrorType.INUSE_VIOLATION;
		}
		return false;
	}

	private IIcfg<IcfgLocation> petrify(final IIcfg<IcfgLocation> icfg, final int numberOfThreadInstances) {
		assert IcfgUtils.isConcurrent(icfg) : "Petrification unnecessary for sequential programs";

		mLogger.info("Constructing petrified ICFG for " + numberOfThreadInstances + " thread instances.");
		final IcfgPetrifier icfgPetrifier = new IcfgPetrifier(mServices, icfg, numberOfThreadInstances, false);
		final IIcfg<IcfgLocation> petrifiedIcfg = icfgPetrifier.getPetrifiedIcfg();
		mLocationMap = ((BlockEncodingBacktranslator) icfgPetrifier.getBacktranslator()).getLocationMapping();
		mServices.getBacktranslationService().addTranslator(icfgPetrifier.getBacktranslator());
		return petrifiedIcfg;
	}

	private TraceAbstractionBenchmarks createNewBenchmark(final DebugIdentifier ident, final IIcfg<IcfgLocation> icfg) {
		final List<TraceAbstractionBenchmarks> benchmarks = mStatistics.computeIfAbsent(ident, x -> new ArrayList<>());
		final TraceAbstractionBenchmarks bench = new TraceAbstractionBenchmarks(icfg);
		benchmarks.add(bench);
		return bench;
	}

	private void reportBenchmarkResults() {
		for (final Map.Entry<DebugIdentifier, List<TraceAbstractionBenchmarks>> entry : mStatistics.entrySet()) {
			final DebugIdentifier ident = entry.getKey();

			int i = 1;
			for (final TraceAbstractionBenchmarks benchmark : entry.getValue()) {
				final String shortDescription = getBenchmarkDescription(ident, i);
				mResultReporter
						.reportResult(new StatisticsResult<>(Activator.PLUGIN_NAME, shortDescription, benchmark));
				i++;
			}
		}
	}

	private void recordLocationResult(final IcfgLocation loc, final IResult res) {
		final IcfgLocation original = getOriginalLocation(loc);
		final IResult old = mResultsPerLocation.get(original);
		if (old == null) {
			mResultsPerLocation.put(original, res);
		} else {
			mResultsPerLocation.put(original, ResultUtil.combineLocationResults(old, res));
		}
	}

	private IcfgLocation getOriginalLocation(final IcfgLocation loc) {
		if (mLocationMap == null) {
			return loc;
		}
		return mLocationMap.getOrDefault(loc, loc);
	}

	private void reportLocationResults() {
		// Determine if we were unable to prove thread instance sufficiency. This could e.g. be due to a counterexample,
		// a timeout, or a unprovable trace.
		final boolean couldBeInsufficient =
				mResultsPerLocation.entrySet().stream().anyMatch(entry -> isInsufficientThreadsLocation(entry.getKey())
						&& !(entry.getValue() instanceof PositiveResult<?>));

		for (final Map.Entry<IcfgLocation, IResult> entry : mResultsPerLocation.entrySet()) {
			final boolean output;
			if (couldBeInsufficient) {
				// Output all non-positive results (for real error locations, and for insufficient threads). Results for
				// insufficient threads are reported to explain why a determination on some real error locations could
				// potentially not be made.
				output = !(entry.getValue() instanceof PositiveResult<?>);
			} else {
				// Output only results for real error locations. (If not mentioned, the user can simply assume that
				// sufficient thread instances were used.)
				output = !isInsufficientThreadsLocation(entry.getKey());
			}

			if (output) {
				mResultReporter.reportResult(entry.getValue());
			}
		}
	}

	private String getBenchmarkDescription(final DebugIdentifier ident, final int numThreads) {
		final String description;
		if (ident instanceof AllErrorsAtOnceDebugIdentifier) {
			description = "Ultimate Automizer benchmark data";
		} else if (ident instanceof ThreadInstanceDebugIdentifier) {
			description = "Ultimate Automizer benchmark data for errors in thread instance: " + ident;
		} else if (ident instanceof InUseDebugIdentifier) {
			description = "Ultimate Automizer benchmark data for thread instance sufficiency";
		} else if (isInsufficientThreadsIdentifier(ident)) {
			description = "Ultimate Automizer benchmark data for thread instance sufficiency: " + ident;
		} else {
			description = "Ultimate Automizer benchmark data for error location: " + ident;
		}

		if (mIsConcurrent) {
			return description + " with " + numThreads + " thread instances";
		}
		return description;
	}

	private static boolean isAuxilliaryProcedure(final String proc) {
		return ULTIMATE_INIT.equals(proc) || ULTIMATE_START.equals(proc);
	}

	/**
	 * @return the root of the CFG.
	 */
	public IElement getRootOfNewModel() {
		return mRootOfNewModel;
	}

	private static <L extends IIcfgTransition<?>> boolean hasSufficientThreadInstances(final CegarLoopResult<L> clres) {
		return clres.getResults().entrySet().stream().filter(a -> a.getValue().getResult() == Result.UNSAFE)
				.noneMatch(a -> isInsufficientThreadsLocation(a.getKey()));
	}

	private static boolean isInsufficientThreadsLocation(final IcfgLocation loc) {
		final Check check = Check.getAnnotation(loc);
		return check != null && check.getSpec().contains(Spec.SUFFICIENT_THREAD_INSTANCES);
	}

	public static final class AllErrorsAtOnceDebugIdentifier extends DebugIdentifier {

		public static final AllErrorsAtOnceDebugIdentifier INSTANCE = new AllErrorsAtOnceDebugIdentifier();

		private AllErrorsAtOnceDebugIdentifier() {
			// singleton constructor
		}

		@Override
		public String toString() {
			return "AllErrorsAtOnce";
		}
	}

	private static final class ThreadInstanceDebugIdentifier extends StringDebugIdentifier {
		private ThreadInstanceDebugIdentifier(final String threadInstance) {
			super(threadInstance);
		}
	}

	public static final class InUseDebugIdentifier extends DebugIdentifier {

		public static final InUseDebugIdentifier INSTANCE = new InUseDebugIdentifier();

		private InUseDebugIdentifier() {
			// singleton constructor
		}

		@Override
		public String toString() {
			return "InUseError";
		}
	}
}
