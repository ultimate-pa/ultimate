/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.IRunningTaskStackProvider;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessInvariant;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.InvariantResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ProcedureContractResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultUtil;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UserSpecifiedLimitReachedResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgPetrifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgPetrifier.IcfgConstructionMode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgElement;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.HoareAnnotation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.IcfgAngelicProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.HoareAnnotationChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Concurrency;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.FloydHoareAutomataReuse;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

public class TraceAbstractionStarter<L extends IIcfgTransition<?>> {

	public static final String ULTIMATE_INIT = "ULTIMATE.init";

	public static final String ULTIMATE_START = "ULTIMATE.start";

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	/**
	 * Root Node of this Ultimate model. I use this to store information that should be passed to the next plugin. The
	 * Successors of this node exactly the initial nodes of procedures.
	 */
	private IElement mRootOfNewModel;
	private Result mOverallResult;
	private IElement mArtifact;

	private final List<Pair<AbstractInterpolantAutomaton<L>, IPredicateUnifier>> mFloydHoareAutomataFromOtherErrorLocations;

	private final Class<L> mTransitionClazz;
	private final IPLBECompositionFactory<L> mCompositionFactory;

	public TraceAbstractionStarter(final IUltimateServiceProvider services, final IIcfg<IcfgLocation> icfg,
			final INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> witnessAutomaton,
			final List<INestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile,
			final IPLBECompositionFactory<L> compositionFactory, final Class<L> transitionClazz) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mTransitionClazz = transitionClazz;
		mCompositionFactory = compositionFactory;
		mFloydHoareAutomataFromOtherErrorLocations = new ArrayList<>();
		runCegarLoops(icfg, witnessAutomaton, rawFloydHoareAutomataFromFile);
	}

	private void runCegarLoops(final IIcfg<IcfgLocation> icfg,
			final INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> witnessAutomaton,
			final List<INestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile) {
		final TAPreferences taPrefs = new TAPreferences(mServices);

		final boolean computeHoareAnnotation;
		if (taPrefs.computeHoareAnnotation()
				&& !icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().isEmpty()) {
			mLogger.warn("Switching off computation of Hoare annotation because input is a concurrent program");
			computeHoareAnnotation = false;
		} else {
			computeHoareAnnotation = taPrefs.computeHoareAnnotation();
		}

		String settings = "Automizer settings:";
		settings += " Hoare:" + computeHoareAnnotation;
		settings += " " + (taPrefs.differenceSenwa() ? "SeNWA" : "NWA");
		settings += " Interpolation:" + taPrefs.interpolation();
		settings += " Determinization: " + taPrefs.interpolantAutomatonEnhancement();
		mLogger.info(settings);

		final CfgSmtToolkit csToolkit = icfg.getCfgSmtToolkit();
		final PredicateFactory predicateFactory =
				new PredicateFactory(mServices, csToolkit.getManagedScript(), csToolkit.getSymbolTable());
		TraceAbstractionBenchmarks traceAbstractionBenchmark = new TraceAbstractionBenchmarks(icfg);

		final Map<String, Set<IcfgLocation>> proc2errNodes = icfg.getProcedureErrorNodes();
		final Collection<IcfgLocation> errNodesOfAllProc = new ArrayList<>();
		for (final Collection<IcfgLocation> errNodeOfProc : proc2errNodes.values()) {
			errNodesOfAllProc.addAll(errNodeOfProc);
		}
		mLogger.info("Appying trace abstraction to program that has " + errNodesOfAllProc.size() + " error locations.");

		mOverallResult = Result.SAFE;
		mArtifact = null;
		final IProgressMonitorService progmon = mServices.getProgressMonitorService();
		final int numberOfErrorLocs = errNodesOfAllProc.size();
		if (taPrefs.allErrorLocsAtOnce()) {
			if (taPrefs.hasLimitAnalysisTime()) {
				progmon.addChildTimer(progmon.getTimer(taPrefs.getLimitAnalysisTime() * 1000 * numberOfErrorLocs));
			}
			iterateAllErrorsAtOnce(AllErrorsAtOnceDebugIdentifier.INSTANCE, icfg, taPrefs, predicateFactory,
					traceAbstractionBenchmark, errNodesOfAllProc, witnessAutomaton, rawFloydHoareAutomataFromFile,
					computeHoareAnnotation);
			reportBenchmark(traceAbstractionBenchmark);
			if (taPrefs.hasLimitAnalysisTime()) {
				progmon.removeChildTimer();
			}
		} else {
			int finishedErrorLocs = 1;
			for (final IcfgLocation errorLoc : errNodesOfAllProc) {
				final DebugIdentifier name = errorLoc.getDebugIdentifier();
				final List<IcfgLocation> errorLocs = new ArrayList<>(1);
				errorLocs.add(errorLoc);
				if (taPrefs.hasLimitAnalysisTime()) {
					progmon.addChildTimer(progmon.getTimer(taPrefs.getLimitAnalysisTime() * 1000));
				}
				mServices.getProgressMonitorService().setSubtask(errorLoc.toString());
				final Result result =
						iterate(name, icfg, taPrefs, csToolkit, predicateFactory, traceAbstractionBenchmark, errorLocs,
								witnessAutomaton, rawFloydHoareAutomataFromFile, computeHoareAnnotation);
				mLogger.info(String.format("Result for error location %s was %s (%s/%s)", name, result,
						finishedErrorLocs, numberOfErrorLocs));
				reportBenchmarkForErrLocation(traceAbstractionBenchmark, errorLoc.toString());
				traceAbstractionBenchmark = new TraceAbstractionBenchmarks(icfg);
				if (taPrefs.hasLimitAnalysisTime()) {
					progmon.removeChildTimer();
				}
				finishedErrorLocs++;
			}
		}
		logNumberOfWitnessInvariants(errNodesOfAllProc);
		if (mOverallResult == Result.SAFE) {
			final AllSpecificationsHoldResult result = AllSpecificationsHoldResult
					.createAllSpecificationsHoldResult(Activator.PLUGIN_NAME, errNodesOfAllProc.size());
			reportResult(result);
		}

		mLogger.debug("Compute Hoare Annotation: " + computeHoareAnnotation);
		mLogger.debug("Overall result: " + mOverallResult);
		mLogger.debug("Continue processing: " + mServices.getProgressMonitorService().continueProcessing());
		if (computeHoareAnnotation && mOverallResult != Result.TIMEOUT
				&& !Result.USER_LIMIT_RESULTS.contains(mOverallResult)
				&& mServices.getProgressMonitorService().continueProcessing()) {
			final IBacktranslationService backTranslatorService = mServices.getBacktranslationService();
			createInvariantResults(icfg, csToolkit, backTranslatorService);
			createProcedureContractResults(icfg, backTranslatorService);
		}

		switch (mOverallResult) {
		case SAFE:
		case UNSAFE:
			break;
		case TIMEOUT:
			mLogger.warn("Timeout");
			break;
		case UNKNOWN:
			mLogger.warn("Unable to decide correctness. Please check the following counterexample manually.");
			break;
		default:
			throw new UnsupportedOperationException("Unknown overall result " + mOverallResult);
		}

		mRootOfNewModel = mArtifact;
	}

	private void createInvariantResults(final IIcfg<IcfgLocation> icfg, final CfgSmtToolkit csToolkit,
			final IBacktranslationService backTranslatorService) {
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
			reportResult(invResult);

			if (formula.equals(trueterm)) {
				continue;
			}
			final String inv = backTranslatorService.translateExpressionToString(formula, Term.class);
			new WitnessInvariant(inv).annotate(locNode);
		}
	}

	private void createProcedureContractResults(final IIcfg<IcfgLocation> icfg,
			final IBacktranslationService backTranslatorService) {
		final Map<String, IcfgLocation> finalNodes = icfg.getProcedureExitNodes();
		for (final Entry<String, IcfgLocation> proc : finalNodes.entrySet()) {
			final String procName = proc.getKey();
			if (isAuxilliaryProcedure(procName)) {
				continue;
			}
			final IcfgLocation finalNode = proc.getValue();
			final HoareAnnotation hoare = HoareAnnotation.getAnnotation(finalNode);
			if (hoare != null) {
				final Term formula = hoare.getFormula();
				final ProcedureContractResult<IIcfgElement, Term> result = new ProcedureContractResult<>(
						Activator.PLUGIN_NAME, finalNode, backTranslatorService, procName, formula);

				reportResult(result);
				// TODO: Add setting that controls the generation of those witness invariants
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
			final IAnnotations annot = boogieASTNode.getPayload().getAnnotations().get(Check.class.getName());
			if (annot != null) {
				final Check check = (Check) annot;
				if (check.getSpec().contains(Spec.WITNESS_INVARIANT)) {
					numberOfCheckedInvariants++;
				}
			}
		}
		if (numberOfCheckedInvariants > 0) {
			mLogger.info("Automizer considered " + numberOfCheckedInvariants + " witness invariants");
			mLogger.info("WitnessConsidered=" + numberOfCheckedInvariants);
		}
	}

	private Result iterateAllErrorsAtOnce(final DebugIdentifier name, final IIcfg<IcfgLocation> root,
			final TAPreferences taPrefs, final PredicateFactory predicateFactory,
			final TraceAbstractionBenchmarks taBenchmark, final Collection<IcfgLocation> errorLocs,
			final INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> witnessAutomaton,
			final List<INestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile,
			final boolean computeHoareAnnotation) {
		final CegarLoopResult<L> clres;
		if (root.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().isEmpty()) {
			clres = CegarLoopUtils.getCegarLoopResult(mServices, name, root, taPrefs, predicateFactory, errorLocs,
					witnessAutomaton, rawFloydHoareAutomataFromFile, computeHoareAnnotation, taPrefs.getConcurrency(),
					mCompositionFactory, mTransitionClazz);
		} else {
			int numberOfThreadInstances = 1;
			while (true) {
				mLogger.info("Constructing petrified ICFG for " + numberOfThreadInstances + " thread instances.");
				final IcfgPetrifier icfgPetrifier = new IcfgPetrifier(mServices, root,
						IcfgConstructionMode.ASSUME_THREAD_INSTANCE_SUFFICIENCY, numberOfThreadInstances);
				final IIcfg<IcfgLocation> petrifiedIcfg = icfgPetrifier.getPetrifiedIcfg();
				mServices.getBacktranslationService().addTranslator(icfgPetrifier.getBacktranslator());
				final CfgSmtToolkit cfgSmtToolkit = petrifiedIcfg.getCfgSmtToolkit();
				final PredicateFactory newPredicateFactory = new PredicateFactory(mServices,
						cfgSmtToolkit.getManagedScript(), cfgSmtToolkit.getSymbolTable());
				// TODO: Use ThreadGeneralization here (with a setting!)
				final Set<IcfgLocation> errNodesOfAllProc = petrifiedIcfg.getProcedureErrorNodes().values().stream()
						.flatMap(Set::stream).collect(Collectors.toSet());
				final CegarLoopResult<L> result = CegarLoopUtils.getCegarLoopResult(mServices, name, petrifiedIcfg,
						taPrefs, newPredicateFactory, errNodesOfAllProc, witnessAutomaton,
						rawFloydHoareAutomataFromFile, computeHoareAnnotation, taPrefs.getConcurrency(),
						mCompositionFactory, mTransitionClazz);
				if (hasSufficientThreadInstances(result)) {
					clres = result;
					break;
				}
				mLogger.warn(numberOfThreadInstances
						+ " thread instances were not sufficient, I will increase this number and restart the analysis");
				numberOfThreadInstances++;
				taBenchmark.aggregateBenchmarkData(result.getCegarLoopStatisticsGenerator());
			}
		}
		if (taPrefs.getFloydHoareAutomataReuse() != FloydHoareAutomataReuse.NONE) {
			mFloydHoareAutomataFromOtherErrorLocations.addAll(clres.getFloydHoareAutomata());
		}
		mOverallResult = clres.getOverallResult();
		reportResults(errorLocs, clres, mOverallResult);

		taBenchmark.aggregateBenchmarkData(clres.getCegarLoopStatisticsGenerator());

		mArtifact = clres.getArtifact();
		return mOverallResult;
	}

	private static <L extends IIcfgTransition<?>> boolean hasSufficientThreadInstances(final CegarLoopResult<L> clres) {
		if (clres.getOverallResult() != Result.UNSAFE) {
			return true;
		}
		final AtomicTraceElement<L> te =
				clres.getProgramExecution().getTraceElement(clres.getProgramExecution().getLength() - 1);
		final IcfgLocation tar = te.getTraceElement().getTarget();
		final Check check = Check.getAnnotation(tar);
		return !check.getSpec().contains(Spec.SUFFICIENT_THREAD_INSTANCES);
	}

	private Result iterate(final DebugIdentifier name, final IIcfg<IcfgLocation> root, final TAPreferences taPrefs,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final TraceAbstractionBenchmarks taBenchmark, final Collection<IcfgLocation> errorLocs,
			final INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> witnessAutomaton,
			final List<INestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile,
			final boolean computeHoareAnnotation) {
		IIcfg<IcfgLocation> icfg;
		if (root.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().isEmpty()) {
			icfg = root;
		} else {
			final int numberOfThreadInstances = 3;
			final IcfgPetrifier icfgPetrifier = new IcfgPetrifier(mServices, root,
					IcfgConstructionMode.ASSUME_THREAD_INSTANCE_SUFFICIENCY, numberOfThreadInstances);
			final IIcfg<IcfgLocation> petrifiedIcfg = icfgPetrifier.getPetrifiedIcfg();
			mServices.getBacktranslationService().addTranslator(icfgPetrifier.getBacktranslator());
			icfg = petrifiedIcfg;
		}
		final PredicateFactory newPredicateFactory = new PredicateFactory(mServices,
				icfg.getCfgSmtToolkit().getManagedScript(), icfg.getCfgSmtToolkit().getSymbolTable());
		final BasicCegarLoop<L> basicCegarLoop =
				CegarLoopUtils.constructCegarLoop(mServices, name, icfg, taPrefs, icfg.getCfgSmtToolkit(),
						newPredicateFactory, errorLocs, rawFloydHoareAutomataFromFile, computeHoareAnnotation,
						Concurrency.FINITE_AUTOMATA, mCompositionFactory, mTransitionClazz, witnessAutomaton);
		final Result result = basicCegarLoop.iterate();
		if (result == Result.UNSAFE) {
			final AtomicTraceElement<L> te = basicCegarLoop.getRcfgProgramExecution()
					.getTraceElement(basicCegarLoop.getRcfgProgramExecution().getLength() - 1);
			final IcfgLocation tar = te.getTraceElement().getTarget();
			final Check check = Check.getAnnotation(tar);
			if (check != null && check.getSpec().contains(Spec.SUFFICIENT_THREAD_INSTANCES)) {
				reportResult(new GenericResult(Activator.PLUGIN_ID, "unable to analyze concurrent program",
						"unable to analyze", Severity.WARNING));
				return Result.UNKNOWN;
			}
		}

		basicCegarLoop.finish();
		if (taPrefs.getFloydHoareAutomataReuse() != FloydHoareAutomataReuse.NONE) {
			mFloydHoareAutomataFromOtherErrorLocations.addAll(basicCegarLoop.getFloydHoareAutomata());
		}

		mOverallResult = computeOverallResult(errorLocs, basicCegarLoop, result);
		final IStatisticsDataProvider cegarLoopBenchmarkGenerator = basicCegarLoop.getCegarLoopBenchmark();
		taBenchmark.aggregateBenchmarkData(cegarLoopBenchmarkGenerator);

		mArtifact = basicCegarLoop.getArtifact();
		return result;
	}

	private Result reportResults(final Collection<IcfgLocation> errorLocs, final CegarLoopResult<L> clres,
			final Result result) {
		switch (result) {
		case SAFE:
			reportPositiveResults(errorLocs);
			return mOverallResult;
		case UNSAFE:
			reportCounterexampleResult(clres.getProgramExecution());
			return result;
		case TIMEOUT:
		case USER_LIMIT_ITERATIONS:
		case USER_LIMIT_PATH_PROGRAM:
		case USER_LIMIT_TIME:
		case USER_LIMIT_TRACEHISTOGRAM:
			reportLimitResult(result, errorLocs, clres.getRunningTaskStackProvider());
			return mOverallResult != Result.UNSAFE ? result : mOverallResult;
		case UNKNOWN:
			final IProgramExecution<L, Term> pe = clres.getProgramExecution();
			reportUnproveableResult(pe, clres.getUnprovabilityReasons());
			return mOverallResult != Result.UNSAFE ? result : mOverallResult;
		default:
			throw new IllegalArgumentException();
		}
	}

	private Result computeOverallResult(final Collection<IcfgLocation> errorLocs,
			final BasicCegarLoop<L> basicCegarLoop, final Result result) {
		switch (result) {
		case SAFE:
			reportPositiveResults(errorLocs);
			return mOverallResult;
		case UNSAFE:
			reportCounterexampleResult(basicCegarLoop.getRcfgProgramExecution());
			return result;
		case TIMEOUT:
		case USER_LIMIT_ITERATIONS:
		case USER_LIMIT_PATH_PROGRAM:
		case USER_LIMIT_TIME:
		case USER_LIMIT_TRACEHISTOGRAM:
			reportLimitResult(result, errorLocs, basicCegarLoop.getRunningTaskStackProvider());
			return mOverallResult != Result.UNSAFE ? result : mOverallResult;
		case UNKNOWN:
			final IProgramExecution<L, Term> pe = basicCegarLoop.getRcfgProgramExecution();
			final List<UnprovabilityReason> unprovabilityReasons = new ArrayList<>();
			unprovabilityReasons.add(basicCegarLoop.getReasonUnknown());
			unprovabilityReasons.addAll(UnprovabilityReason.getUnprovabilityReasons(pe));
			reportUnproveableResult(pe, unprovabilityReasons);
			return mOverallResult != Result.UNSAFE ? result : mOverallResult;
		default:
			throw new IllegalArgumentException();
		}
	}

	private void reportPositiveResults(final Collection<IcfgLocation> errorLocs) {
		for (final IcfgLocation errorLoc : errorLocs) {
			final PositiveResult<IIcfgElement> pResult =
					new PositiveResult<>(Activator.PLUGIN_NAME, errorLoc, mServices.getBacktranslationService());
			reportResult(pResult);
		}
	}

	private void reportCounterexampleResult(final IProgramExecution<L, Term> pe) {
		final List<UnprovabilityReason> upreasons = UnprovabilityReason.getUnprovabilityReasons(pe);
		if (!upreasons.isEmpty()) {
			reportUnproveableResult(pe, upreasons);
			return;
		}
		if (isAngelicallySafe(pe)) {
			mLogger.info("Ignoring angelically safe counterexample");
			return;
		}
		reportResult(new CounterExampleResult<>(getErrorPP(pe), Activator.PLUGIN_NAME,
				mServices.getBacktranslationService(), pe));
	}

	private static <L extends IIcfgTransition<?>> boolean isAngelicallySafe(final IProgramExecution<L, Term> pe) {
		if (pe instanceof IcfgAngelicProgramExecution) {
			return !((IcfgAngelicProgramExecution<L>) pe).getAngelicStatus();
		}
		return false;
	}

	private void reportLimitResult(final Result result, final Collection<IcfgLocation> errorLocs,
			final IRunningTaskStackProvider rtsp) {
		for (final IcfgLocation errorIpp : errorLocs) {
			final IResult res = constructLimitResult(mServices, result, rtsp, errorIpp);
			reportResult(res);
		}
	}

	public static IResult constructLimitResult(final IUltimateServiceProvider services, final Result result,
			final IRunningTaskStackProvider rtsp, final IcfgLocation errorIpp) {
		final StringBuilder sb = new StringBuilder();
		sb.append("Unable to prove that ");
		sb.append(ResultUtil.getCheckedSpecification(errorIpp).getPositiveMessage());
		if (errorIpp instanceof BoogieIcfgLocation) {
			final ILocation origin = ((BoogieIcfgLocation) errorIpp).getBoogieASTNode().getLocation();
			sb.append(" (line ").append(origin.getStartLine()).append(").");
		}
		if (rtsp != null) {
			sb.append(" Cancelled ").append(rtsp.printRunningTaskMessage());
		}

		final IResult res;
		if (result == Result.TIMEOUT) {
			res = new TimeoutResultAtElement<>(errorIpp, Activator.PLUGIN_NAME, services.getBacktranslationService(),
					sb.toString());
		} else {
			res = new UserSpecifiedLimitReachedResultAtElement<IElement>(result.toString(), errorIpp,
					Activator.PLUGIN_NAME, services.getBacktranslationService(), sb.toString());
		}
		return res;
	}

	private void reportUnproveableResult(final IProgramExecution<L, Term> pe,
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

	private <T> void reportBenchmarkForErrLocation(final ICsvProviderProvider<T> benchmark,
			final String errLocDescription) {
		final String shortDescription = "Ultimate Automizer benchmark data for error location: " + errLocDescription;
		final StatisticsResult<T> res = new StatisticsResult<>(Activator.PLUGIN_NAME, shortDescription, benchmark);
		reportResult(res);
	}

	private static boolean isAuxilliaryProcedure(final String proc) {
		return ULTIMATE_INIT.equals(proc) || ULTIMATE_START.equals(proc);
	}

	private void reportResult(final IResult res) {
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, res);
	}

	/**
	 * @return the root of the CFG.
	 */
	public IElement getRootOfNewModel() {
		return mRootOfNewModel;
	}

	public static <L extends IIcfgTransition<?>> IcfgLocation getErrorPP(final IProgramExecution<L, Term> pe) {
		final int lastPosition = pe.getLength() - 1;
		final IIcfgTransition<?> last = pe.getTraceElement(lastPosition).getTraceElement();
		return last.getTarget();
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
}
