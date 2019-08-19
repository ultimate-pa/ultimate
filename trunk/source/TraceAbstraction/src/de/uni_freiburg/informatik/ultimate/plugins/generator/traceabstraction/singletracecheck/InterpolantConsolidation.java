/*
 * Copyright (C) 2015 Betim Musa (musab@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarStatisticsType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantConsolidation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.CachingHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.CachingHoareTripleCheckerMap;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceCheck.AllIntegers;
import de.uni_freiburg.informatik.ultimate.util.InCaReCounter;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsGeneratorWithStopwatches;

/**
 * Interpolant Consolidation is a way of either improving a sequence of interpolants or merging several sequences of
 * interpolants into one, which is the disjunction of the sequences. By doing this we get a sequence of interpolants
 * that is weaker than any other of the input sequences. See documentation of B.Musa for more information.
 *
 * @author musab@informatik.uni-freiburg.de
 */
public class InterpolantConsolidation<LETTER extends IIcfgTransition<?>> implements IInterpolantGenerator<LETTER> {

	private static final boolean PRINT_DEBUG_INFORMATION = false;
	private static final boolean PRINT_DIFFERENCE_AUTOMATA = false;
	private static final boolean USE_CONSOLIDATION_IN_NON_EMPTY_CASE = false;

	private final IInterpolantGenerator<LETTER> mInterpolatingTraceCheck;
	private final IPredicate mPrecondition;
	private final IPredicate mPostcondition;
	private final SortedMap<Integer, IPredicate> mPendingContexts;
	private IPredicate[] mConsolidatedInterpolants;
	private final TAPreferences mTaPrefs;
	private final NestedWord<LETTER> mTrace;
	private final IUltimateServiceProvider mServices;
	private final CfgSmtToolkit mCsToolkit;
	private final IPredicateUnifier mPredicateUnifier;
	private final PredicateFactory mPredicateFactory;
	private final ILogger mLogger;
	private final CachingHoareTripleChecker mHoareTripleChecker;
	private final InterpolantComputationStatus mInterpolantComputationStatus;

	protected final InterpolantConsolidationBenchmarkGenerator mInterpolantConsolidationBenchmarkGenerator;
	private boolean mInterpolantsConsolidationSuccessful = false;

	public InterpolantConsolidation(final IPredicate precondition, final IPredicate postcondition,
			final SortedMap<Integer, IPredicate> pendingContexts, final NestedWord<LETTER> trace,
			final CfgSmtToolkit csToolkit, final ModifiableGlobalsTable modifiableGlobalsTable,
			final IUltimateServiceProvider services, final ILogger logger, final PredicateFactory predicateFactory,
			final IPredicateUnifier predicateUnifier, final IInterpolantGenerator<LETTER> tc,
			final TAPreferences taPrefs) throws AutomataOperationCanceledException {
		mPrecondition = precondition;
		mPostcondition = postcondition;
		mPendingContexts = pendingContexts;
		mTrace = trace;
		mCsToolkit = csToolkit;
		mServices = services;
		mLogger = logger;
		mPredicateFactory = predicateFactory;
		mPredicateUnifier = predicateUnifier;
		mInterpolatingTraceCheck = tc;
		mConsolidatedInterpolants = new IPredicate[mTrace.length() - 1];
		mTaPrefs = taPrefs;
		mInterpolantConsolidationBenchmarkGenerator = new InterpolantConsolidationBenchmarkGenerator();

		final IHoareTripleChecker ehtc = TraceAbstractionUtils.constructEfficientHoareTripleChecker(services,
				TraceAbstractionPreferenceInitializer.HoareTripleChecks.INCREMENTAL, mCsToolkit, mPredicateUnifier);
		mHoareTripleChecker = new CachingHoareTripleCheckerMap(services, ehtc, mPredicateUnifier);

		final InterpolantComputationStatus status = mInterpolatingTraceCheck.getInterpolantComputationStatus();
		if (status.wasComputationSuccesful()) {
			computeInterpolants(new AllIntegers());

		}
		mInterpolantComputationStatus = status;
	}

	protected void computeInterpolants(final Set<Integer> interpolatedPositions)
			throws AutomataOperationCanceledException {
		// Start the stopwatch to measure the time we need for interpolant consolidation
		mInterpolantConsolidationBenchmarkGenerator.start(InterpolantConsolidationBenchmarkType.s_TimeOfConsolidation);

		// 1. Build the path automaton for the given trace mTrace
		final PathProgramAutomatonConstructor<LETTER> ppc = new PathProgramAutomatonConstructor<>();
		final INestedWordAutomaton<LETTER, IPredicate> pathprogramautomaton =
				ppc.constructAutomatonFromGivenPath(mTrace, mServices, mCsToolkit, mPredicateFactory, mTaPrefs);

		// 2. Build the finite automaton (former interpolant path automaton) for the given Floyd-Hoare annotation
		final NestedWordAutomaton<LETTER, IPredicate> interpolantAutomaton = constructInterpolantAutomaton(mTrace,
				mCsToolkit, mPredicateFactory, mTaPrefs, mServices, mInterpolatingTraceCheck);
		// 3. Determinize the finite automaton from step 2.
		final DeterministicInterpolantAutomaton<LETTER> interpolantAutomatonDeterminized =
				new DeterministicInterpolantAutomaton<>(mServices, mCsToolkit, mHoareTripleChecker,
						interpolantAutomaton, mPredicateUnifier, false, false // PREDICATE_ABSTRACTION_CANNIBALIZE
																				// = false (default)
				);

		final PredicateFactoryForInterpolantConsolidation pfconsol = new PredicateFactoryForInterpolantConsolidation(
				mCsToolkit, mPredicateFactory, mTaPrefs.computeHoareAnnotation());

		final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata =
				new PredicateFactoryForInterpolantAutomata(mCsToolkit.getManagedScript(), mPredicateFactory,
						mTaPrefs.computeHoareAnnotation());

		final PowersetDeterminizer<LETTER, IPredicate> psd2 =
				new PowersetDeterminizer<>(interpolantAutomatonDeterminized, true, predicateFactoryInterpolantAutomata);

		try {
			// 4. Compute the difference between the path automaton and the determinized
			// finite automaton (from step 3)
			final Difference<LETTER, IPredicate> diff = new Difference<>(new AutomataLibraryServices(mServices),
					pfconsol /* PredicateFactory for Refinement */, pathprogramautomaton,
					interpolantAutomatonDeterminized, psd2, false /* explointSigmaStarConcatOfIA */ );
			if (PRINT_DIFFERENCE_AUTOMATA) {
				// Needed for debug
				final AutomatonDefinitionPrinter<LETTER, IPredicate> pathAutomatonPrinter =
						new AutomatonDefinitionPrinter<>(new AutomataLibraryServices(mServices), "PathAutomaton",
								Format.ATS, pathprogramautomaton);
				final AutomatonDefinitionPrinter<LETTER, IPredicate> interpolantAutomatonPrinter =
						new AutomatonDefinitionPrinter<>(new AutomataLibraryServices(mServices),
								"InterpolantAutomatonNonDet", Format.ATS, interpolantAutomaton);
				final AutomatonDefinitionPrinter<LETTER, IPredicate> interpolantAutomatonPrinterDet =
						new AutomatonDefinitionPrinter<>(new AutomataLibraryServices(mServices),
								"InterpolantAutomatonDet", Format.ATS, interpolantAutomatonDeterminized);
				final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> diffAutomaton = diff.getResult();
				final AutomatonDefinitionPrinter<LETTER, IPredicate> diffAutomatonPrinter =
						new AutomatonDefinitionPrinter<>(new AutomataLibraryServices(mServices), "DifferenceAutomaton",
								Format.ATS, diffAutomaton);
				mLogger.debug(pathAutomatonPrinter.getDefinitionAsString());
				mLogger.debug(interpolantAutomatonPrinter.getDefinitionAsString());
				mLogger.debug(interpolantAutomatonPrinterDet.getDefinitionAsString());
				mLogger.debug(diffAutomatonPrinter.getDefinitionAsString());
			}
			mHoareTripleChecker.releaseLock();
			// 5. Check if difference is empty
			final IsEmpty<LETTER, IPredicate> empty =
					new IsEmpty<>(new AutomataLibraryServices(mServices), diff.getResult());
			if (!empty.getResult()) {
				if (!USE_CONSOLIDATION_IN_NON_EMPTY_CASE) {
					if (mInterpolatingTraceCheck instanceof TraceCheckSpWp) {
						// If the forwards predicates is a perfect sequence of interpolants, then use it, otherwise use
						// the sequence of backwards predicates
						final TraceCheckSpWp<LETTER> tc = (TraceCheckSpWp<LETTER>) mInterpolatingTraceCheck;
						final boolean forwardsPredicatesPerfect = tc.isForwardSequencePerfect();
						if (forwardsPredicatesPerfect) {
							mConsolidatedInterpolants = tc.getForwardPredicates().toArray(new IPredicate[0]);
						} else {
							mConsolidatedInterpolants = tc.getBackwardPredicates().toArray(new IPredicate[0]);
						}
					} else {
						mConsolidatedInterpolants = mInterpolatingTraceCheck.getInterpolants();
					}

					// Stop the time for interpolant consolidation
					mInterpolantConsolidationBenchmarkGenerator
							.stop(InterpolantConsolidationBenchmarkType.s_TimeOfConsolidation);
					return;
				}
				final Collection<IPredicate> pathautomatonFinalStates = pathprogramautomaton.getFinalStates();
				if (pathautomatonFinalStates.size() > 1) {
					throw new AssertionError("path automaton has more than 1 final state");
				}
				final Collection<IPredicate> interpolantautomatonFinalStates = interpolantAutomaton.getFinalStates();
				if (interpolantautomatonFinalStates.size() > 1) {
					throw new AssertionError("interpolant automaton has more than 1 final state");
				}
				final IPredicate[] pathautomatonFinalState = pathautomatonFinalStates.toArray(new IPredicate[1]);
				final IPredicate[] interpolantautomatonFinalState =
						interpolantautomatonFinalStates.toArray(new IPredicate[1]);

				final IPredicate specialState =
						pfconsol.getIntersectedPredicate(pathautomatonFinalState[0], interpolantautomatonFinalState[0]);
				final Map<IPredicate, Integer> stateToLevel = new HashMap<>();
				final Set<IPredicate> goodStates =
						getDiffAutomatonGoodStates(diff.getResult(), specialState, stateToLevel);
				if (PRINT_DEBUG_INFORMATION) {
					mLogger.debug("Printing good states...");
					for (final IPredicate p : goodStates) {
						mLogger.debug(p);
					}

				}
				final Set<IPredicate> badStates = diff.getResult().getStates();
				badStates.removeAll(goodStates); // Bad states are the result of the set-difference of all states and
													// the good states.
				// Delete bad predicates from consolidation
				pfconsol.removeBadPredicates(badStates);
				// Remove consolidated predicates that have different levels
				pfconsol.removeConsolidatedPredicatesOnDifferentLevels(stateToLevel);
			}
		} catch (final AutomataOperationCanceledException e) {
			if (mLogger.isInfoEnabled()) {
				mLogger.info("Timeout while computing interpolants");
			}
			throw e;
		} catch (final AutomataLibraryException e) {
			if (mLogger.isWarnEnabled()) {
				mLogger.warn("Error while computing interpolants");
			}
			throw new AssertionError(e);
		}

		// 6. Interpolant Consolidation step
		final List<IPredicate> pathProgramLocations = ppc.getPositionsToStates();
		final Map<IPredicate, Set<IPredicate>> locationsToSetOfPredicates = pfconsol.getLocationsToSetOfPredicates();

		final Set<IPredicate> interpolantsBeforeConsolidation = interpolantAutomaton.getStates();
		final Set<IPredicate> interpolantsAfterConsolidation = new HashSet<>();

		mInterpolantConsolidationBenchmarkGenerator.incrementDiffAutomatonEmpty_Counter();

		mConsolidatedInterpolants = new IPredicate[mTrace.length() - 1];

		computeConsolidatedInterpolants(pathProgramLocations, locationsToSetOfPredicates,
				interpolantsBeforeConsolidation, interpolantsAfterConsolidation, mHoareTripleChecker);

		assert TraceCheckUtils.checkInterpolantsInductivityBackward(Arrays.asList(mConsolidatedInterpolants), mTrace,
				mPrecondition, mPostcondition, mPendingContexts, "CP", mCsToolkit, mLogger,
				mCsToolkit.getManagedScript()) : "invalid Hoare triple in consolidated interpolants";
		final int numOfDisjunctionsGreaterOne = (int) mInterpolantConsolidationBenchmarkGenerator
				.getValue(InterpolantConsolidationBenchmarkType.s_DisjunctionsGreaterOneCounter);
		// InterpolantConsolidation was successful only if there was at least one consolidation with at least two
		// predicates.
		if (numOfDisjunctionsGreaterOne > 0) {
			mInterpolantsConsolidationSuccessful = true;
		}

		if (PRINT_DEBUG_INFORMATION) {
			mLogger.debug("Interpolants before consolidation:");
			printArray(
					interpolantAutomaton.getStates().toArray(new IPredicate[interpolantAutomaton.getStates().size()]));
			mLogger.debug("Interpolants after consolidation:");
			printArray(interpolantsAfterConsolidation.toArray(new IPredicate[interpolantsAfterConsolidation.size()]));
		}

	}

	private Set<IPredicate> getDiffAutomatonGoodStates(final INestedWordAutomaton<LETTER, IPredicate> diffAutomaton,
			final IPredicate specialState, final Map<IPredicate, Integer> stateToLevel) {
		final Set<IPredicate> visitedStates = new HashSet<>(); // The visited states are the good states
		final LinkedList<IPredicate> statesToVisit = new LinkedList<>();
		final LinkedList<IPredicate> predecessorsToVisit = new LinkedList<>();
		statesToVisit.add(specialState);
		int currentLevel = 0;
		final int levelIncrement = 1;
		final Map<Integer, Set<IPredicate>> levelToStates = new HashMap<>();
		while (!statesToVisit.isEmpty()) {
			final IPredicate currentState = statesToVisit.removeFirst();
			if (!visitedStates.contains(currentState)) {
				visitedStates.add(currentState);
			} else {
				// Remove state from incorrect level
				final int incorrectLvl = stateToLevel.get(currentState);
				final Set<IPredicate> statesAtIncorrectLvl = levelToStates.get(incorrectLvl);
				if (statesAtIncorrectLvl != null) {
					statesAtIncorrectLvl.remove(currentState);
				}
			}

			final Set<IPredicate> predecessors = getPredecessorsOfState(diffAutomaton, currentState);
			for (final IPredicate p : predecessors) {
				if (!currentState.equals(p)) { // Avoid self-loops
					if (!visitedStates.contains(p)) {
						predecessorsToVisit.addLast(p);
					} else {
						final Set<IPredicate> predecessorsOfP = getPredecessorsOfState(diffAutomaton, p);
						// Add predecessor p to states to be visited only if not all of its predecessors has been
						// already visited
						// This is another step to avoid cycles
						if (!visitedStates.containsAll(predecessorsOfP)) {
							predecessorsToVisit.addLast(p);
						}
					}
				}
			}

			Set<IPredicate> statesAtThisLevel = levelToStates.get(currentLevel);
			if (statesAtThisLevel == null) {
				statesAtThisLevel = new HashSet<>();
				statesAtThisLevel.add(currentState);
				levelToStates.put(currentLevel, statesAtThisLevel);
			} else {
				statesAtThisLevel.add(currentState);
			}
			stateToLevel.put(currentState, currentLevel);

			if (statesToVisit.isEmpty()) {
				for (final IPredicate p : predecessorsToVisit) {
					statesToVisit.addLast(p);
				}
				predecessorsToVisit.clear();
				currentLevel = currentLevel + levelIncrement;
			}
		}
		// Remove all states that are mapped to different levels
		for (int lvl = 0; lvl < currentLevel; lvl++) {
			final Set<IPredicate> statesAtLvl = levelToStates.get(lvl);
			if (statesAtLvl != null && statesAtLvl.size() == 1) {
				visitedStates.removeAll(statesAtLvl);
			}
		}
		return visitedStates;
	}

	private Set<IPredicate> getPredecessorsOfState(final INestedWordAutomaton<LETTER, IPredicate> diffAutomaton,
			final IPredicate currentState) {
		final Set<IPredicate> preds = new HashSet<>();
		for (final IncomingInternalTransition<LETTER, IPredicate> it : diffAutomaton
				.internalPredecessors(currentState)) {
			preds.add(it.getPred());
		}
		for (final IncomingCallTransition<LETTER, IPredicate> ict : diffAutomaton.callPredecessors(currentState)) {
			preds.add(ict.getPred());
		}
		for (final IncomingReturnTransition<LETTER, IPredicate> irt : diffAutomaton.returnPredecessors(currentState)) {
			preds.add(irt.getLinPred());
		}
		return preds;
	}

	/**
	 * Create for every location of the path program the disjunction of all predicates associated with that location.
	 *
	 * @param pathProgramLocations
	 * @param locationsToSetOfPredicates
	 * @param interpolantsBeforeConsolidation
	 *            - the set containing every interpolant from all sequences of interpolants, it is used only for
	 *            benchmarks.
	 * @param interpolantsAfterConsolidation
	 *            - a list of predicates that is initially empty, but gets filled with consolidated interpolants
	 * @param htc
	 */
	private void computeConsolidatedInterpolants(final List<IPredicate> pathProgramLocations,
			final Map<IPredicate, Set<IPredicate>> locationsToSetOfPredicates,
			final Set<IPredicate> interpolantsBeforeConsolidation, final Set<IPredicate> interpolantsAfterConsolidation,
			final IHoareTripleChecker htc) {

		final Map<IPredicate, IPredicate> locationsToConsolidatedInterpolants = new HashMap<>();

		int disjunctionsGreaterOneCounter = 0;
		int newlyCreatedInterpolants = 0;
		// Init it with max. number of interpolants and decrement it every time you encounter an interpolant that
		// has existed before consolidation.
		int interpolantsDropped = mTrace.length() - 1;
		for (int i = 0; i < mConsolidatedInterpolants.length; i++) {
			final IPredicate loc = pathProgramLocations.get(i + 1);
			if (!locationsToConsolidatedInterpolants.containsKey(loc)) {
				// Compute the disjunction of the predicates for location i
				final Set<IPredicate> predicatesForThisLocation = locationsToSetOfPredicates.get(loc);

				assert predicatesForThisLocation != null : "The set of predicates for the current location is null!";

				final IPredicate[] predicatesForThisLocationAsArray =
						predicatesForThisLocation.toArray(new IPredicate[predicatesForThisLocation.size()]);

				if (predicatesForThisLocation.size() > 1) {

					// Case: consolidation is successful. We have at least 2 predicates which are connected by
					// disjunction.
					// Update benchmarks
					disjunctionsGreaterOneCounter++;

					// TermVarsProc predicatesForThisLocationConsolidated =
					// mCsToolkit.getPredicateFactory().or(predicatesForThisLocationAsArray);
					// // Store the consolidated (the disjunction of the predicates for the current location)
					// mConsolidatedInterpolants[i] =
					// mPredicateUnifier.getOrConstructPredicate(predicatesForThisLocationConsolidated);
					mConsolidatedInterpolants[i] =
							mPredicateUnifier.getOrConstructPredicateForDisjunction(predicatesForThisLocation);

					if (!interpolantsBeforeConsolidation.contains(mConsolidatedInterpolants[i])) {

						// If the consolidated interpolant is not contained in the interpolants before consolidation,
						// then
						// the consolidated interpolant is new.
						newlyCreatedInterpolants++;
					}
					locationsToConsolidatedInterpolants.put(loc, mConsolidatedInterpolants[i]);

				} else {
					mConsolidatedInterpolants[i] = predicatesForThisLocationAsArray[0];
				}
				if (interpolantsBeforeConsolidation.contains(mConsolidatedInterpolants[i])) {
					// If current interpolant is contained in the interpolants before consolidation, then the number of
					// interpolants dropped decreases.
					interpolantsDropped--;
				}
				interpolantsAfterConsolidation.add(mConsolidatedInterpolants[i]);

			} else {
				mConsolidatedInterpolants[i] = locationsToConsolidatedInterpolants.get(loc);
			}

		}
		final int differenceOfInterpolantsBeforeAfter =
				interpolantsBeforeConsolidation.size() - interpolantsAfterConsolidation.size();
		mInterpolantConsolidationBenchmarkGenerator.setInterpolantConsolidationData(disjunctionsGreaterOneCounter,
				newlyCreatedInterpolants, interpolantsDropped, differenceOfInterpolantsBeforeAfter,
				htc.getEdgeCheckerBenchmark());
		// Stop the time for interpolant consolidation
		mInterpolantConsolidationBenchmarkGenerator.stop(InterpolantConsolidationBenchmarkType.s_TimeOfConsolidation);
	}

	private void printArray(final IPredicate[] interpolants) {
		for (int i = 0; i < interpolants.length; i++) {
			mLogger.debug(Integer.toString(i) + ". " + interpolants[i].toString());
		}

	}

	public List<IPredicate> getInterpolantsOfType_I() {
		if (mInterpolatingTraceCheck instanceof TraceCheckSpWp) {
			final TraceCheckSpWp<LETTER> tcspwp = (TraceCheckSpWp<LETTER>) mInterpolatingTraceCheck;
			if (tcspwp.wasForwardPredicateComputationRequested()) {
				return tcspwp.getForwardPredicates();
			}
			return Arrays.asList(tcspwp.getInterpolants());
		}
		return Arrays.asList(mInterpolatingTraceCheck.getInterpolants());
	}

	public List<IPredicate> getInterpolantsOfType_II() {
		if (mInterpolatingTraceCheck instanceof TraceCheckSpWp) {
			final TraceCheckSpWp<LETTER> tcspwp = (TraceCheckSpWp<LETTER>) mInterpolatingTraceCheck;
			if (tcspwp.wasBackwardSequenceConstructed()) {
				return tcspwp.getBackwardPredicates();
			}
			return Arrays.asList(tcspwp.getInterpolants());
		}
		return Arrays.asList(mInterpolatingTraceCheck.getInterpolants());
	}

	public boolean consolidationSuccessful() {
		return mInterpolantsConsolidationSuccessful;
	}

	/**
	 * Construct a finite automaton for the given Floyd-Hoare annotation.
	 *
	 * @param trace
	 *            - the trace from which the automaton is constructed.
	 * @param interpolantGenerator
	 *            - contains the Floyd-Hoare annotation (the interpolants) for which the automaton is constructed.
	 * @return
	 */
	private NestedWordAutomaton<LETTER, IPredicate> constructInterpolantAutomaton(final NestedWord<LETTER> trace,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactor, final TAPreferences taPrefs,
			final IUltimateServiceProvider services, final IInterpolantGenerator<LETTER> interpolantGenerator) {
		// Set the alphabet
		final Set<LETTER> internalAlphabet = new HashSet<>();
		final Set<LETTER> callAlphabet = new HashSet<>();
		final Set<LETTER> returnAlphabet = new HashSet<>();
		for (int i = 0; i < trace.length(); i++) {
			if (trace.isInternalPosition(i)) {
				internalAlphabet.add(trace.getSymbol(i));
			} else if (trace.isCallPosition(i)) {
				callAlphabet.add(trace.getSymbol(i));
			} else if (trace.isReturnPosition(i)) {
				returnAlphabet.add(trace.getSymbol(i));
			} else {
				throw new UnsupportedOperationException(
						"Symbol at position " + i + " is neither internal, call, nor return symbol!");
			}
		}

		final IEmptyStackStateFactory<IPredicate> predicateFactoryFia = new PredicateFactoryForInterpolantAutomata(
				csToolkit.getManagedScript(), predicateFactor, taPrefs.computeHoareAnnotation());

		final NestedWordAutomaton<LETTER, IPredicate> nwa =
				new NestedWordAutomaton<>(new AutomataLibraryServices(services),
						new VpAlphabet<>(internalAlphabet, callAlphabet, returnAlphabet), predicateFactoryFia);
		// Set the initial and the final state of the automaton
		nwa.addState(true, false, interpolantGenerator.getPrecondition());
		nwa.addState(false, true, interpolantGenerator.getPostcondition());
		boolean nwaStatesAndTransitionsAdded = false;

		if (interpolantGenerator instanceof TraceCheckSpWp) {
			final TraceCheckSpWp<LETTER> tcSpWp = (TraceCheckSpWp<LETTER>) interpolantGenerator;
			if (tcSpWp.wasForwardPredicateComputationRequested() && tcSpWp.wasBackwardSequenceConstructed()) {
				nwaStatesAndTransitionsAdded = true;
				// Add states and transitions corresponding to forwards predicates
				addStatesAndCorrespondingTransitionsFromGivenInterpolants(nwa, interpolantGenerator.getPrecondition(),
						interpolantGenerator.getPostcondition(), tcSpWp.getForwardPredicates(), trace);
				// Add states and transitions corresponding to backwards predicates
				addStatesAndCorrespondingTransitionsFromGivenInterpolants(nwa, interpolantGenerator.getPrecondition(),
						interpolantGenerator.getPostcondition(), tcSpWp.getBackwardPredicates(), trace);
			}
		}

		if (!nwaStatesAndTransitionsAdded) {
			addStatesAndCorrespondingTransitionsFromGivenInterpolants(nwa, interpolantGenerator.getPrecondition(),
					interpolantGenerator.getPostcondition(), Arrays.asList(interpolantGenerator.getInterpolants()),
					trace);
		}
		return nwa;
	}

	public IPredicate getInterpolantAtPosition(final int i, final IPredicate precondition,
			final IPredicate postcondition, final List<IPredicate> interpolants) {
		if (i < 0) {
			throw new AssertionError("index beyond precondition");
		} else if (i == 0) {
			return precondition;
		} else if (i <= interpolants.size()) {
			return interpolants.get(i - 1);
		} else if (i == interpolants.size() + 1) {
			return postcondition;
		} else {
			throw new AssertionError("index beyond postcondition");
		}
	}

	private void addStatesAndCorrespondingTransitionsFromGivenInterpolants(
			final NestedWordAutomaton<LETTER, IPredicate> nwa, final IPredicate precondition,
			final IPredicate postcondition, final List<IPredicate> interpolants, final NestedWord<LETTER> trace) {
		for (int i = 0; i < trace.length(); i++) {
			final IPredicate pred = getInterpolantAtPosition(i, precondition, postcondition, interpolants);
			final IPredicate succ = getInterpolantAtPosition(i + 1, precondition, postcondition, interpolants);

			assert nwa.getStates().contains(pred);
			if (!nwa.getStates().contains(succ)) {
				nwa.addState(false, false, succ);
			}
			if (trace.isCallPosition(i)) {
				nwa.addCallTransition(pred, trace.getSymbol(i), succ);
			} else if (trace.isReturnPosition(i)) {
				assert !trace.isPendingReturn(i);
				final int callPos = trace.getCallPosition(i);
				final IPredicate hierPred =
						getInterpolantAtPosition(callPos, precondition, postcondition, interpolants);
				nwa.addReturnTransition(pred, hierPred, trace.getSymbol(i), succ);
			} else {
				assert trace.isInternalPosition(i);
				nwa.addInternalTransition(pred, trace.getSymbol(i), succ);
			}
		}
	}

	@Override
	public IPredicate[] getInterpolants() {
		return mConsolidatedInterpolants;
	}

	@Override
	public List<LETTER> getTrace() {
		return mTrace.asList();
	}

	@Override
	public IPredicate getPrecondition() {
		return mPrecondition;
	}

	@Override
	public IPredicate getPostcondition() {
		return mPostcondition;
	}

	@Override
	public Map<Integer, IPredicate> getPendingContexts() {
		return mPendingContexts;
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}

	@Override
	public boolean isPerfectSequence() {
		final BackwardCoveringInformation bci = TraceCheckUtils.computeCoverageCapability(mServices, this, mLogger);
		final boolean isPerfect = bci.getPotentialBackwardCoverings() == bci.getSuccessfullBackwardCoverings();
		return isPerfect;
	}

	@Override
	public InterpolantComputationStatus getInterpolantComputationStatus() {
		return mInterpolantComputationStatus;
	}

	public InterpolantConsolidationBenchmarkGenerator getInterpolantConsolidationBenchmarks() {
		return mInterpolantConsolidationBenchmarkGenerator;
	}

	public CachingHoareTripleChecker getHoareTripleChecker() {
		return mHoareTripleChecker;
	}

	// Benchmarks Section
	public static class InterpolantConsolidationBenchmarkType implements IStatisticsType {
		private static InterpolantConsolidationBenchmarkType s_Instance = new InterpolantConsolidationBenchmarkType();

		/* Keys */
		// Counts how often the difference automaton has been empty
		protected final static String s_DifferenceAutomatonEmptyCounter = "DifferenceAutomatonEmptyCounter";
		// protected final static String s_SumOfPredicatesConsolidated = "SumOfPredicatesConsolidated";

		protected final static String s_DisjunctionsGreaterOneCounter = "DisjunctionsGreaterOneCounter";

		// protected final static String s_SumOfInterpolantsBefore = "SumOfInterpolantsBefore";
		// protected final static String s_SumOfInterpolantsAfterConsoli = "SumOfInterpolantsAfterConsoli";
		protected final static String s_NewlyCreatedInterpolants = "NewlyCreatedInterpolants";

		protected final static String s_InterpolantsDropped = "InterpolantsDropped";

		protected final static String s_DifferenceBeforeAfter = "DifferenceOfInterpolantsBeforeAfter";

		protected final static String s_NumberOfHoareTripleChecks = "NumOfHoareTripleChecks";

		protected final static String s_TimeOfConsolidation = "TimeOfConsolidation";

		public static InterpolantConsolidationBenchmarkType getInstance() {
			return s_Instance;
		}

		@Override
		public Collection<String> getKeys() {
			final ArrayList<String> result = new ArrayList<>();
			result.add(s_DisjunctionsGreaterOneCounter);
			result.add(s_DifferenceBeforeAfter);
			result.add(s_NumberOfHoareTripleChecks);
			result.add(s_TimeOfConsolidation);
			result.add(s_NewlyCreatedInterpolants);
			result.add(s_InterpolantsDropped);
			result.add(s_DifferenceAutomatonEmptyCounter);
			return result;
		}

		@Override
		public Object aggregate(final String key, final Object value1, final Object value2) {
			switch (key) {
			case s_NewlyCreatedInterpolants:
			case s_InterpolantsDropped:
			case s_DifferenceBeforeAfter:
			case s_DifferenceAutomatonEmptyCounter:
			case s_DisjunctionsGreaterOneCounter: {
				final int result = (int) value1 + (int) value2;
				return result;
			}
			case s_TimeOfConsolidation: {
				final long result = (long) value1 + (long) value2;
				return result;
			}
			case s_NumberOfHoareTripleChecks:
				final InCaReCounter counter1 = (InCaReCounter) value1;
				counter1.add((InCaReCounter) value2);
				return counter1;
			default:
				throw new AssertionError("unknown key");
			}
		}

		@Override
		public String prettyprintBenchmarkData(final IStatisticsDataProvider benchmarkData) {
			final StringBuilder sb = new StringBuilder();

			sb.append("\t").append(s_DifferenceAutomatonEmptyCounter).append(": ");
			sb.append((int) benchmarkData.getValue(s_DifferenceAutomatonEmptyCounter));

			sb.append("\t").append(s_DisjunctionsGreaterOneCounter).append(": ");
			sb.append((int) benchmarkData.getValue(s_DisjunctionsGreaterOneCounter));

			sb.append("\t").append(s_NumberOfHoareTripleChecks).append(": ");
			sb.append(benchmarkData.getValue(s_NumberOfHoareTripleChecks));

			sb.append("\t").append(s_InterpolantsDropped).append(": ");
			sb.append((int) benchmarkData.getValue(s_InterpolantsDropped));

			sb.append("\t").append(s_NewlyCreatedInterpolants).append(": ");
			sb.append((int) benchmarkData.getValue(s_NewlyCreatedInterpolants));

			sb.append("\t").append(s_DifferenceBeforeAfter).append(": ");
			sb.append((int) benchmarkData.getValue(s_DifferenceBeforeAfter));

			sb.append("\t").append(s_TimeOfConsolidation).append(": ");
			final Long timeOfInterpolantConsolidation = (Long) benchmarkData.getValue(s_TimeOfConsolidation);
			sb.append(CegarStatisticsType.prettyprintNanoseconds(timeOfInterpolantConsolidation));
			return sb.toString();
		}

	}

	public static class InterpolantConsolidationBenchmarkGenerator extends StatisticsGeneratorWithStopwatches
			implements IStatisticsDataProvider {
		private int mDisjunctionsGreaterOneCounter = 0;
		private int mDifferenceBeforeAfter = 0;
		private int mNewlyCreatedInterpolants = 0;
		private int mInterpolantsDropped = 0;
		// Contains the number of hoare triple checks (i.e. num of sats + num of unsats + num of unknowns)
		// that are made by the interpolant consolidation
		private InCaReCounter mNumOfHoareTripleChecks = new InCaReCounter();
		private int mDiffAutomatonEmpty_Counter = 0;

		public void setInterpolantConsolidationData(final int disjunctionsGreaterOneCounter,
				final int newlyCreatedInterpolants, final int interpolantsDropped,
				final int differenceOfNumOfInterpolantsBeforeAfter, final HoareTripleCheckerStatisticsGenerator htcbg) {
			mDisjunctionsGreaterOneCounter = disjunctionsGreaterOneCounter;
			mDifferenceBeforeAfter = differenceOfNumOfInterpolantsBeforeAfter;
			mNumOfHoareTripleChecks = htcbg.getSolverCounterSat();
			mNumOfHoareTripleChecks.add(htcbg.getSolverCounterUnsat());
			mNumOfHoareTripleChecks.add(htcbg.getSolverCounterUnknown());
			mNewlyCreatedInterpolants = newlyCreatedInterpolants;
			mInterpolantsDropped = interpolantsDropped;
		}

		public void incrementDiffAutomatonEmpty_Counter() {
			mDiffAutomatonEmpty_Counter++;
		}

		@Override
		public Collection<String> getKeys() {
			return InterpolantConsolidationBenchmarkType.getInstance().getKeys();
		}

		@Override
		public Object getValue(final String key) {
			switch (key) {
			case InterpolantConsolidationBenchmarkType.s_NewlyCreatedInterpolants:
				return mNewlyCreatedInterpolants;
			case InterpolantConsolidationBenchmarkType.s_InterpolantsDropped:
				return mInterpolantsDropped;
			case InterpolantConsolidationBenchmarkType.s_DisjunctionsGreaterOneCounter:
				return mDisjunctionsGreaterOneCounter;
			case InterpolantConsolidationBenchmarkType.s_DifferenceBeforeAfter:
				return mDifferenceBeforeAfter;
			case InterpolantConsolidationBenchmarkType.s_NumberOfHoareTripleChecks:
				return mNumOfHoareTripleChecks;
			case InterpolantConsolidationBenchmarkType.s_TimeOfConsolidation:
				try {
					return getElapsedTime(key);
				} catch (final StopwatchStillRunningException e) {
					throw new AssertionError("clock still running: " + key);
				}
			case InterpolantConsolidationBenchmarkType.s_DifferenceAutomatonEmptyCounter:
				return mDiffAutomatonEmpty_Counter;
			default:
				throw new AssertionError("unknown data");
			}
		}

		@Override
		public IStatisticsType getBenchmarkType() {
			return InterpolantConsolidationBenchmarkType.getInstance();
		}

		@Override
		public String[] getStopwatches() {
			return new String[] { InterpolantConsolidationBenchmarkType.s_TimeOfConsolidation };
		}
	}
}
