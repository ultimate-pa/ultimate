/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.NamedAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.AutomatonWithImplicitSelfloops;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze.SymbolType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.ComplementDD;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DeterminizeDD;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.PetriNetUtils;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.Difference.LoopSyncMethod;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.DifferencePairwiseOnDemand;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.RemoveRedundantFlow;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.FinitePrefix2PetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder.EventOrderEnum;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException.UserDefinedLimit;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.ILooperCheck;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PetriCegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PetriCegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.automataminimization.AutomataMinimizationStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.util.HistogramOfIterable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

public class CegarLoopForPetriNet<L extends IIcfgTransition<?>>
		extends BasicCegarLoop<L, BoundedPetriNet<L, IPredicate>> {

	public enum SizeReduction {
		REMOVE_DEAD, REMOVE_REDUNDANT_FLOW
	}

	private static final boolean USE_ON_DEMAND_RESULT = false;

	private static final boolean DEBUG_WRITE_NET_HASH_CODES = false;

	/**
	 * Write result of RemoveUnreachable to file if runtime of this operation in seconds is greater than this number.
	 */
	private static final int DEBUG_DUMP_REMOVEUNREACHABLEINPUT_THRESHOLD = 24 * 60 * 60;

	/**
	 * Write result of RemoveUnreachable to file if runtime of this operation in seconds is greater than this number.
	 */
	private static final int DEBUG_DUMP_DRYRUNRESULT_THRESHOLD = 24 * 60 * 60;

	private static final boolean USE_COUNTEREXAMPLE_CACHE = true;

	public int mCoRelationQueries = 0;
	/**
	 * Alternative measure to
	 * {@link CegarLoopStatisticsDefinitions#BiggestAbstraction} which currently
	 * counts the number of places.
	 * TODO 20220821 Matthias: Find out whether counting transitions instead of
	 * places is helpful. An alternative might be to count flow. In the long
	 * run the most suitable measure should be utilized in the statistics.
	 */
	public int mBiggestAbstractionTransitions;
	/**
	 * Do not enhance the interpolant automaton into a total automaton but construct the enhancement only on-demand and
	 * add only transitions that will be needed for the difference.
	 */
	private final boolean mEnhanceInterpolantAutomatonOnDemand = true;
	/**
	 * Remove unreachable nodes of mAbstraction in each iteration.
	 */
	private final boolean mRemoveDead = false;
	private final boolean mRemoveRedundantFlow = false;

	private final PetriCegarLoopStatisticsGenerator mPetriClStatisticsGenerator;

	private Set<IPredicate> mProgramPointPlaces;

	private final CounterexampleCache<L> mCounterexampleCache;

	public CegarLoopForPetriNet(final DebugIdentifier name, final BoundedPetriNet<L, IPredicate> initialAbstraction,
			final IIcfg<?> rootNode, final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final TAPreferences taPrefs, final Set<IcfgLocation> errorLocs, final IUltimateServiceProvider services,
			final Class<L> transitionClazz, final PredicateFactoryRefinement stateFactoryForRefinement) {
		super(name, initialAbstraction, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs,
				taPrefs.interpolation(), false, Collections.emptySet(), services, transitionClazz,
				stateFactoryForRefinement);
		mPetriClStatisticsGenerator = new PetriCegarLoopStatisticsGenerator(mCegarLoopBenchmark);
		mCounterexampleCache = new CounterexampleCache<>();

		if (DEBUG_WRITE_NET_HASH_CODES) {
			mLogger.debug(PetriNetUtils.printHashCodesOfInternalDataStructures(mAbstraction));
		}
		mProgramPointPlaces = mAbstraction.getPlaces();
	}

	@Override
	protected boolean isAbstractionEmpty() throws AutomataOperationCanceledException {
		if (USE_COUNTEREXAMPLE_CACHE && mIteration != 0) {
			mCounterexample = mCounterexampleCache.getCounterexample();
		} else {
			final boolean cutOffSameTrans = mPref.cutOffRequiresSameTransition();
			final EventOrderEnum eventOrder = mPref.eventOrder();

			mPetriClStatisticsGenerator.start(PetriCegarLoopStatisticsDefinitions.EmptinessCheckTime.toString());
			PetriNetUnfolder<L, IPredicate> unf;
			try {
				unf = new PetriNetUnfolder<>(new AutomataLibraryServices(getServices()), mAbstraction, eventOrder,
						cutOffSameTrans, true);
			} catch (final PetriNetNot1SafeException e) {
				throw new UnsupportedOperationException(e.getMessage());
			} finally {
				mPetriClStatisticsGenerator.stop(PetriCegarLoopStatisticsDefinitions.EmptinessCheckTime.toString());
			}
			final BranchingProcess<L, IPredicate> finPrefix = unf.getFinitePrefix();
			mCoRelationQueries +=
					finPrefix.getCoRelation().getQueryCounterYes() + finPrefix.getCoRelation().getQueryCounterNo();
			mCounterexample = unf.getAcceptingRun();
		}
		if (mCounterexample == null) {
			return true;
		}
		if (mPref.dumpAutomata()) {
			mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.DumpTime);
			mDumper.dumpNestedRun(mCounterexample);
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.DumpTime);
		}
		mLogger.info("Found error trace");

		if (mLogger.isDebugEnabled()) {
			mLogger.debug(mCounterexample.getWord());
		}
		final HistogramOfIterable<L> traceHistogram = new HistogramOfIterable<>(mCounterexample.getWord());
		mCegarLoopBenchmark.reportTraceHistogramMaximum(traceHistogram.getMax());
		if (mLogger.isInfoEnabled()) {
			mLogger.info("trace histogram " + traceHistogram.toString());
		}

		if (mPref.hasLimitTraceHistogram() && traceHistogram.getMax() > mPref.getLimitTraceHistogram()) {
			final String taskDescription =
					"bailout by trace histogram " + traceHistogram.toString() + " in iteration " + mIteration;
			throw new TaskCanceledException(UserDefinedLimit.TRACE_HISTOGRAM, getClass(), taskDescription);
		}
		return false;
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		final IHoareTripleChecker htc = getHoareTripleChecker();
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		try {
			// Determinize the interpolant automaton
			final INestedWordAutomaton<L, IPredicate> dia;
			final Pair<INestedWordAutomaton<L, IPredicate>, DifferencePairwiseOnDemand<L, IPredicate, ?>> enhancementResult =
					enhanceAnddeterminizeInterpolantAutomaton(mInterpolAutomaton, htc,
							mRefinementResult.getPredicateUnifier().getCoverageRelation());
			dia = enhancementResult.getFirst();
			if (USE_COUNTEREXAMPLE_CACHE) {
				final PetriNetRun<L, IPredicate> run =
						enhancementResult.getSecond().getFinitePrefixOfDifference().getAcceptingRun();
				mCounterexampleCache.setCounterexample(run);
			}

			if (mPref.dumpAutomata()) {
				final String filename = new SubtaskIterationIdentifier(mTaskIdentifier, getIteration())
						+ "_AbstractionAfterDifferencePairwiseOnDemand";
				super.writeAutomatonToFile(enhancementResult.getSecond().getResult(), filename);
			}

			// Complement the interpolant automaton
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> nia =
					new ComplementDD<>(new AutomataLibraryServices(getServices()), mPredicateFactoryInterpolantAutomata,
							dia).getResult();
			// TODO 2018-08-11 Matthias: Complement not needed since we compute difference.
			// Furthermore there is a problem because we would have to concatenate operand
			// with some ∑^* automaton first and we do not yet have an implementation for
			// that.
			// assert !accepts(mServices, nia, mCounterexample.getWord(), false) :
			// "Complementation broken!";
			// mLogger.info("Complemented interpolant automaton has " + nia.size() + "
			// states");

			if (mIteration <= mPref.watchIteration() && mPref.artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON) {
				mArtifactAutomaton = nia;
			}
			if (USE_ON_DEMAND_RESULT) {
				mAbstraction = enhancementResult.getSecond().getResult();
			} else {
				final Difference<L, IPredicate, ?> diff = new Difference<>(new AutomataLibraryServices(getServices()),
						mPredicateFactoryInterpolantAutomata, mAbstraction, dia, LoopSyncMethod.HEURISTIC,
						enhancementResult.getSecond(), true);
				mLogger.info(diff.getAutomataOperationStatistics());
				mAbstraction = diff.getResult();
			}
			mCegarLoopBenchmark.reportInterpolantAutomatonStates(dia.size());
		} finally {
			mCegarLoopBenchmark.addEdgeCheckerData(htc.getStatistics());
			mCegarLoopBenchmark
					.addPredicateUnifierData(mRefinementResult.getPredicateUnifier().getPredicateUnifierBenchmark());
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		}

		if (mPref.dumpAutomata()) {
			final String filename =
					new SubtaskIterationIdentifier(mTaskIdentifier, getIteration()) + "_AbstractionAfterDifference";
			super.writeAutomatonToFile(mAbstraction, filename);
		}

		mLogger.info(mProgramPointPlaces.size() + " programPoint places, "
				+ (mAbstraction.getPlaces().size() - mProgramPointPlaces.size()) + " predicate places.");

		if (mRemoveDead) {
			final Triple<BoundedPetriNet<L, IPredicate>, AutomataMinimizationStatisticsGenerator, Long> minimizationResult =
					doSizeReduction(mAbstraction, SizeReduction.REMOVE_DEAD);
			mCegarLoopBenchmark.addAutomataMinimizationData(minimizationResult.getSecond());
			if (mPref.dumpAutomata()
					|| minimizationResult.getThird() > DEBUG_DUMP_REMOVEUNREACHABLEINPUT_THRESHOLD * 1_000_000_000L) {
				final String filename = new SubtaskIterationIdentifier(mTaskIdentifier, getIteration())
						+ "_AbstractionBeforeRemoveDead";
				super.writeAutomatonToFile(mAbstraction, filename);
			}
			mAbstraction = minimizationResult.getFirst();
		}
		if (mRemoveRedundantFlow) {
			final Triple<BoundedPetriNet<L, IPredicate>, AutomataMinimizationStatisticsGenerator, Long> minimizationResult =
					doSizeReduction(mAbstraction, SizeReduction.REMOVE_REDUNDANT_FLOW);
			mCegarLoopBenchmark.addAutomataMinimizationData(minimizationResult.getSecond());
			if (mPref.dumpAutomata()
					|| minimizationResult.getThird() > DEBUG_DUMP_REMOVEUNREACHABLEINPUT_THRESHOLD * 1_000_000_000L) {
				final String filename = new SubtaskIterationIdentifier(mTaskIdentifier, getIteration())
						+ "_AbstractionBeforeRemoveRedundantFlow";
				super.writeAutomatonToFile(mAbstraction, filename);
			}
			mAbstraction = minimizationResult.getFirst();
		}

		if (mPref.unfoldingToNet()) {
			final int flowBefore = mAbstraction.size();
			mLogger.info(mProgramPointPlaces.size() + " programPoint places, "
					+ (mAbstraction.getPlaces().size() - mProgramPointPlaces.size()) + " predicate places.");
			mPetriClStatisticsGenerator.start(PetriCegarLoopStatisticsDefinitions.BackfoldingUnfoldingTime.toString());
			PetriNetUnfolder<L, IPredicate> unf;
			try {
				final boolean cutOffSameTrans = mPref.cutOffRequiresSameTransition();
				final EventOrderEnum eventOrder = mPref.eventOrder();
				unf = new PetriNetUnfolder<>(new AutomataLibraryServices(getServices()), mAbstraction, eventOrder,
						cutOffSameTrans, false);
			} catch (final PetriNetNot1SafeException e) {
				throw new UnsupportedOperationException(e.getMessage());
			} catch (final AutomataOperationCanceledException aoce) {
				throw aoce;
			} finally {
				mPetriClStatisticsGenerator
						.stop(PetriCegarLoopStatisticsDefinitions.BackfoldingUnfoldingTime.toString());
			}
			mPetriClStatisticsGenerator.start(PetriCegarLoopStatisticsDefinitions.BackfoldingTime.toString());
			final FinitePrefix2PetriNet<L, IPredicate> fp2pn =
					new FinitePrefix2PetriNet<>(new AutomataLibraryServices(getServices()), mStateFactoryForRefinement,
							unf.getFinitePrefix(), true);
			assert fp2pn.checkResult(mPredicateFactoryResultChecking) : fp2pn.getClass().getSimpleName() + " failed";
			mAbstraction = fp2pn.getResult();
			final Set<IPredicate> oldProgramPointPlaces = mProgramPointPlaces;
			mProgramPointPlaces = fp2pn.getOldToNewPlaces().projectToRange(oldProgramPointPlaces);
			final int flowAfterwards = mAbstraction.size();
			mPetriClStatisticsGenerator.reportFlowIncreaseByBackfolding(flowAfterwards - flowBefore);
			mPetriClStatisticsGenerator.stop(PetriCegarLoopStatisticsDefinitions.BackfoldingTime.toString());
			mLogger.info(mProgramPointPlaces.size() + " programPoint places, "
					+ (mAbstraction.getPlaces().size() - mProgramPointPlaces.size()) + " predicate places.");
			// The following two variables control a potential optimization whose idea is
			// the following. Our backfolding duplicates program points because we hope that
			// this saves steps in the next unfolding and allow us to remove flow partially
			// (flow of one copy). However, it could also be helpful to remerge copies
			// afterwards. If `remergeProgramPoints` is set, we merge all copies that belong
			// to the same program point. If this variable is not set, we merge all copies
			// that belong to the same object but only if this object is not a program
			// point.
			// TODO 20220821 Matthias: Evaluate whether these options are useful. If yes,
			// add settings for these local variables. If these options are complete
			// useless, the code should be removed.
			final boolean partialRemerge = false;
			final boolean remergeProgramPoints = true;
			if (partialRemerge) {
				final IPetriNet<L, IPredicate> abstractionAsNet = mAbstraction;
				final UnionFind<IPredicate> uf = new UnionFind<>();
				for (final Entry<IPredicate, HashSet<IPredicate>> entry : fp2pn.getOldToNewPlaces().entrySet()) {
					if (remergeProgramPoints ^ oldProgramPointPlaces.contains(entry.getKey())) {
						uf.addEquivalenceClass(ImmutableSet.of(entry.getValue()));
					}
				}
				final Map<IPredicate, IPredicate> placeMap = PetriNetUtils
						.mergePlaces(new HashSet<>(abstractionAsNet.getPlaces()), uf);
				final IPetriNet<L, IPredicate> res = PetriNetUtils.mergePlaces(new AutomataLibraryServices(mServices),
						abstractionAsNet, placeMap);
				mAbstraction = (BoundedPetriNet<L, IPredicate>) res;
				mProgramPointPlaces = mProgramPointPlaces.stream().map(placeMap::get).collect(Collectors.toSet());
				mLogger.info(mProgramPointPlaces.size() + " programPoint places, "
						+ (mAbstraction.getPlaces().size() - mProgramPointPlaces.size()) + " predicate places.");
			}
		}

		mCegarLoopBenchmark.reportAbstractionSize(mAbstraction.size(), mIteration);
		mBiggestAbstractionTransitions = mAbstraction.getTransitions().size();

		assert !acceptsPetriViaFA(getServices(), mAbstraction, mCounterexample.getWord()) : "Intersection broken!";

		// int[] statistic = mAbstraction.transitions();
		// s_Logger.debug("Abstraction has " +
		// mAbstraction.getAllStates().size() + "states, " +
		// statistic[0] + " internal transitions " + statistic[1] +
		// "call transitions " + statistic[2]+ " return transitions ");

		if (mIteration <= mPref.watchIteration()
				&& (mPref.artifact() == Artifact.ABSTRACTION || mPref.artifact() == Artifact.RCFG)) {
			mArtifactAutomaton = mAbstraction;
		}
		if (mPref.dumpAutomata()) {
			final String filename = "Abstraction" + mIteration;
			writeAutomatonToFile(mAbstraction, filename);
		}
		return true;
	}

	private Triple<BoundedPetriNet<L, IPredicate>, AutomataMinimizationStatisticsGenerator, Long>
			doSizeReduction(final BoundedPetriNet<L, IPredicate> input, final SizeReduction method)
					throws AutomataOperationCanceledException, PetriNetNot1SafeException, AssertionError {
		final long automataMinimizationTime;
		final long start = System.nanoTime();
		long statesRemovedByMinimization = 0;
		long transitionsRemovedByMinimization = 0;
		long flowRemovedByMinimization = 0;
		boolean nontrivialMinimizaton = false;
		mPetriClStatisticsGenerator.start(PetriCegarLoopStatisticsDefinitions.RemoveRedundantFlowTime.toString());
		final AutomataMinimizationStatisticsGenerator amsg;
		final BoundedPetriNet<L, IPredicate> reducedNet;
		try {
			final int placesBefore = input.getPlaces().size();
			final int transitionsBefore = input.getTransitions().size();
			final int flowBefore = input.size();
			switch (method) {
			case REMOVE_DEAD:
				reducedNet = new de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.RemoveDead<>(
						new AutomataLibraryServices(getServices()), input, null, true).getResult();
				break;
			case REMOVE_REDUNDANT_FLOW:
				final Set<IPredicate> redundancyCandidates = input.getPlaces().stream()
						.filter(x -> !mProgramPointPlaces.contains(x)).collect(Collectors.toSet());
				reducedNet =
						new RemoveRedundantFlow<>(new AutomataLibraryServices(getServices()), input, null, null, null)
								.getResult();
				break;
			default:
				throw new AssertionError("unknown value " + method);
			}
			final int placesAfterwards = reducedNet.getPlaces().size();
			final int transitionsAfterwards = reducedNet.getTransitions().size();
			final int flowAfterwards = reducedNet.size();
			statesRemovedByMinimization = placesBefore - placesAfterwards;
			transitionsRemovedByMinimization = transitionsBefore - transitionsAfterwards;
			flowRemovedByMinimization = flowBefore - flowAfterwards;
			// if (transitionsAfterwards != transitionsBefore) {
			// throw new AssertionError("removed transitions: " +
			// transitionsRemovedByMinimization + " Iteration "
			// + mIteration + " Abstraction has " + mAbstraction.sizeInformation());
			// }
			nontrivialMinimizaton = true;
		} finally {
			automataMinimizationTime = System.nanoTime() - start;
			amsg = new AutomataMinimizationStatisticsGenerator(automataMinimizationTime, true, nontrivialMinimizaton,
					flowRemovedByMinimization);
			mPetriClStatisticsGenerator.stop(PetriCegarLoopStatisticsDefinitions.RemoveRedundantFlowTime.toString());
		}
		final Triple<BoundedPetriNet<L, IPredicate>, AutomataMinimizationStatisticsGenerator, Long> minimizationResult =
				new Triple<>(reducedNet, amsg, automataMinimizationTime);
		return minimizationResult;
	}

	protected Pair<INestedWordAutomaton<L, IPredicate>, DifferencePairwiseOnDemand<L, IPredicate, ?>>
			enhanceAnddeterminizeInterpolantAutomaton(final INestedWordAutomaton<L, IPredicate> interpolAutomaton,
					final IHoareTripleChecker htc, final IPredicateCoverageChecker coverage)
					throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		mLogger.debug("Start determinization");
		final INestedWordAutomaton<L, IPredicate> dia;
		final DifferencePairwiseOnDemand<L, IPredicate, ?> dpod;
		switch (mPref.interpolantAutomatonEnhancement()) {
		case NONE:
			final PowersetDeterminizer<L, IPredicate> psd =
					new PowersetDeterminizer<>(interpolAutomaton, true, mPredicateFactoryInterpolantAutomata);
			final DeterminizeDD<L, IPredicate> dabps = new DeterminizeDD<>(new AutomataLibraryServices(getServices()),
					mPredicateFactoryInterpolantAutomata, interpolAutomaton, psd);
			dia = dabps.getResult();
			dpod = null;
			break;
		case PREDICATE_ABSTRACTION:
			final DeterministicInterpolantAutomaton<L> raw = new DeterministicInterpolantAutomaton<>(getServices(),
					mCsToolkit, htc, interpolAutomaton, mRefinementResult.getPredicateUnifier(), false, false);
			if (mEnhanceInterpolantAutomatonOnDemand) {
				final Set<L> universalSubtrahendLoopers = determineUniversalSubtrahendLoopers(
						mAbstraction.getAlphabet(), interpolAutomaton.getStates(), htc, coverage);
				mLogger.info("Number of universal loopers: " + universalSubtrahendLoopers.size() + " out of "
						+ mAbstraction.getAlphabet().size());
				final NestedWordAutomaton<L, IPredicate> ia = (NestedWordAutomaton<L, IPredicate>) interpolAutomaton;
				for (final IPredicate state : ia.getStates()) {
					for (final L letter : universalSubtrahendLoopers) {
						ia.addInternalTransition(state, letter, state);
					}
				}
				final long start = System.nanoTime();
				try {
					dpod = new DifferencePairwiseOnDemand<>(new AutomataLibraryServices(getServices()),
							(IPetriNet<L, IPredicate>) mAbstraction, raw, universalSubtrahendLoopers);
				} catch (final AutomataOperationCanceledException tce) {
					final String taskDescription = generateOnDemandEnhancementCanceledMessage(interpolAutomaton,
							universalSubtrahendLoopers, mAbstraction.getAlphabet(), mIteration);
					tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
					throw tce;
				} finally {
					raw.switchToReadonlyMode();
				}
				final AutomatonWithImplicitSelfloops<L, IPredicate> awis = new AutomatonWithImplicitSelfloops<>(
						new AutomataLibraryServices(getServices()), raw, universalSubtrahendLoopers);
				dia = new RemoveUnreachable<>(new AutomataLibraryServices(getServices()), awis).getResult();
				final long end = System.nanoTime();
				if (end - start > DEBUG_DUMP_DRYRUNRESULT_THRESHOLD * 1_000_000_000L) {
					final String filename = new SubtaskIterationIdentifier(mTaskIdentifier, getIteration())
							+ "_DifferencePairwiseOnDemandInput";
					final String atsHeaderMessage = "inputs of difference operation in iteration " + mIteration;
					final String atsCode = "PetriNet diff = differencePairwiseOnDemand(net, nwa);";
					super.writeAutomataToFile(filename, atsHeaderMessage, atsCode,
							new NamedAutomaton<>("net", mAbstraction), new NamedAutomaton<>("nwa", dia));
				}
			} else {
				dpod = null;
				try {
					dia = new RemoveUnreachable<>(new AutomataLibraryServices(getServices()), raw).getResult();
				} catch (final AutomataOperationCanceledException aoce) {
					final RunningTaskInfo rti = new RunningTaskInfo(getClass(),
							"enhancing interpolant automaton that has " + interpolAutomaton.getStates().size()
									+ " states and an alphabet of " + mAbstraction.getAlphabet().size() + " letters");
					throw new ToolchainCanceledException(aoce, rti);
				}
			}
			final double dfaTransitionDensity = new Analyze<>(new AutomataLibraryServices(getServices()), dia, false)
					.getTransitionDensity(SymbolType.INTERNAL);
			mLogger.info("DFA transition density " + dfaTransitionDensity);
			if (mPref.dumpAutomata()) {
				final String filename =
						new SubtaskIterationIdentifier(mTaskIdentifier, getIteration()) + "_EagerFloydHoareAutomaton";
				super.writeAutomatonToFile(dia, filename);
			}
			break;
		default:
			throw new UnsupportedOperationException();
		}

		if (mComputeHoareAnnotation) {
			assert new InductivityCheck<>(getServices(), dia, false, true,
					new IncrementalHoareTripleChecker(super.mCsToolkit, false)).getResult() : "Not inductive";
		}
		if (mPref.dumpAutomata()) {
			final String filename = "InterpolantAutomatonDeterminized_Iteration" + mIteration;
			writeAutomatonToFile(dia, filename);
		}
		// assert accepts(mServices, dia, mCounterexample.getWord(),
		// true) : "Counterexample not accepted by determinized interpolant automaton: "
		// + mCounterexample.getWord();
		mLogger.debug("Sucessfully determinized");
		return new Pair<>(dia, dpod);
	}

	private String generateOnDemandEnhancementCanceledMessage(
			final INestedWordAutomaton<L, IPredicate> interpolAutomaton, final Set<L> universalSubtrahendLoopers,
			final Set<L> alphabet, final int iteration) {
		return "enhancing Floyd-Hoare automaton (" + interpolAutomaton.getStates().size() + "states, "
				+ universalSubtrahendLoopers.size() + "/" + alphabet.size() + " universal loopers) in iteration "
				+ iteration;
	}

	private Set<L> determineUniversalSubtrahendLoopers(final Set<L> alphabet, final Set<IPredicate> states,
			final IHoareTripleChecker htc, final IPredicateCoverageChecker coverage) {
		ILooperCheck<L> looperCheck;
		switch (mPref.looperCheck()) {
		case SEMANTIC:
			looperCheck = new ILooperCheck.HoareLooperCheck<>(htc, coverage);
			break;
		case SYNTACTIC:
			looperCheck = new ILooperCheck.IndependentLooperCheck<>();
			break;
		default:
			throw new AssertionError("Unsupported looper check");
		}

		return alphabet.stream().filter(letter -> looperCheck.isUniversalLooper(letter, states) == LBool.UNSAT)
				.collect(Collectors.toSet());
	}

	@Override
	protected void computeIcfgHoareAnnotation() {
		throw new UnsupportedOperationException("Petri net based analysis cannot compute Hoare annotation.");
	}

	@Override
	protected void constructErrorAutomaton() throws AutomataOperationCanceledException {
		throw new UnsupportedOperationException("Error automata not supported for " + CegarLoopForPetriNet.class);
	}

	private boolean acceptsPetriViaFA(final IUltimateServiceProvider services,
			final IAutomaton<L, IPredicate> automaton, final Word<L> word)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		final NestedWord<L> nw = NestedWord.nestedWord(word);
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> petriNetAsFA =
				new PetriNet2FiniteAutomaton<>(new AutomataLibraryServices(services), mPredicateFactoryResultChecking,
						(IPetriNet<L, IPredicate>) automaton).getResult();
		return super.accepts(services, petriNetAsFA, nw, false);
	}

	@Override
	public IStatisticsDataProvider getCegarLoopBenchmark() {
		return mPetriClStatisticsGenerator;
	}

	private static final class CounterexampleCache<L extends IIcfgTransition<?>> {
		private PetriNetRun<L, IPredicate> mCounterexample;

		public PetriNetRun<L, IPredicate> getCounterexample() {
			return mCounterexample;
		}

		public void setCounterexample(final PetriNetRun<L, IPredicate> counterexample) {
			mCounterexample = counterexample;
		}
	}

}
