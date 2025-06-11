/*
 * Copyright (C) 2025 Matthias Zumkeller
 * Copyright (C) 2025 University of Freiburg
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.TotalizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.UnionNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IUnionStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireComputation;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireToOwickiGries;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.LegalEmpireToOG;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.LegalFocus;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.ModularEmpireAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.ModularEmpireAutomaton.State;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.PetriOwickiGries;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.Region;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.TimeTracker;

public class LegalFocusOwickiGries<L extends IAction, P> implements IPetriNetProofProducer<L, P> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final IPetriNet<L, P> mProgram;
	private final ManagedScript mMgdScript;
	private final IIcfgSymbolTable mSymbolTable;
	private final Set<String> mProcedures;
	private final ModifiableGlobalsTable mModifiableGlobals;
	private final boolean mUseTrivialFocus;
	private PredicateFactory mFactory;

	private BranchingProcess<L, P> mRefinedUnfolding;

	private final Statistics mStatistics;
	private final IUnionStateFactory<List<IPredicate>> mProofUnionFactory;

	private Function<Transition<L, P>, Transition<L, P>> mDiff2OriginalTransition = Function.identity();
	private INwaOutgoingLetterAndTransitionProvider<L, List<IPredicate>> mProofProduct;
	private int mNumProofs = 0;
	private OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> mOwickiGries;

	public LegalFocusOwickiGries(final IUltimateServiceProvider services, final IPetriNet<L, P> program,
			final CfgSmtToolkit csToolkit, final PredicateFactory factory, final boolean useTrivialLegalFocus) {
		this(services, program, csToolkit.getManagedScript(), csToolkit.getSymbolTable(), csToolkit.getProcedures(),
				csToolkit.getModifiableGlobalsTable(), factory, useTrivialLegalFocus);
	}

	public LegalFocusOwickiGries(final IUltimateServiceProvider services, final IPetriNet<L, P> program,
			final ManagedScript mgdScript, final IIcfgSymbolTable symbolTable, final Set<String> procedures,
			final ModifiableGlobalsTable modifiableGlobals, final PredicateFactory factory,
			final boolean useTrivialLegalFocus) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(getClass());
		mProgram = program;
		mMgdScript = mgdScript;
		mSymbolTable = symbolTable;
		mProcedures = procedures;
		mModifiableGlobals = modifiableGlobals;
		mProofUnionFactory = new ProofUnionFactory();
		mStatistics = new Statistics(mLogger);
		mUseTrivialFocus = useTrivialLegalFocus;
		mFactory = factory;
	}

	@Override
	public void refine(final IPredicateUnifier unifier, final INestedWordAutomaton<L, IPredicate> interpolantAutomaton,
			final Map<Transition<L, P>, Transition<L, P>> transitionBacktranslation) {
		mDiff2OriginalTransition = mDiff2OriginalTransition.compose(transitionBacktranslation::get);
		final var convertedAutomaton = convertPredicatesToList(interpolantAutomaton);
		mNumProofs++;
		if (mProofProduct == null) {
			mProofProduct = convertedAutomaton;
		} else {
			final var initialTrueState1 =
					DataStructureUtils.getOneAndOnly(mProofProduct.getInitialStates(), "initial state");
			final var totalizedProduct = new TotalizeNwa<>(mProofProduct, initialTrueState1, false);

			final var initialTrueState2 =
					DataStructureUtils.getOneAndOnly(convertedAutomaton.getInitialStates(), "initial state");
			final var totalizedProof = new TotalizeNwa<>(convertedAutomaton, initialTrueState2, false);
			try {
				mProofProduct = new UnionNwa<>(totalizedProduct, totalizedProof, mProofUnionFactory, false);
			} catch (final AutomataLibraryException e) {
				throw new AssertionError(e);
			}
		}
	}

	@Override
	public boolean isReadyToComputeProof() {
		return true;
	}

	@Override
	public OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> getOrComputeProof() {
		final var possibleInterferences = PetriOwickiGries.getPossibleInterferences(mRefinedUnfolding,
				mProgram.getPlaces(), mDiff2OriginalTransition);

		final NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>> empireAutomaton;
		mStatistics.startEmpireComputation();
		try {
			empireAutomaton = getEmpireAutomaton();
		} finally {
			mStatistics.stopEmpireComputation();
		}

		final LegalFocus<L, P> legalFocus;
		mStatistics.startFocusComputation();
		try {
			mLogger.info("Computing focus ...");
			legalFocus = mUseTrivialFocus ? new TrivialLegalFocus<>(mProgram)
					: new LegalFocus<>(empireAutomaton, mProgram, mProofProduct, mNumProofs);
		} finally {
			mStatistics.stopFocusComputation();
		}

		mStatistics.startOwickiGriesComputation();
		try {
			final var annotationConstruction =
					getOwickiGriesAnnotation(possibleInterferences, empireAutomaton, legalFocus);
			mOwickiGries = annotationConstruction.getAnnotation();
		} finally {
			mStatistics.stopOwickiGriesComputation();
		}

		assert checkOwickiGriesValidity(mOwickiGries) : "Owicki Gries annotation is invalid";
		return mOwickiGries;
	}

	private Map<List<IPredicate>, IPredicate> listStateToPredicate() {
		NestedWordAutomatonReachableStates<L, List<IPredicate>> automatonReachableStates;
		try {
			automatonReachableStates =
					new NestedWordAutomatonReachableStates<>(new AutomataLibraryServices(mServices), mProofProduct);

		} catch (final AutomataOperationCanceledException aoce) {
			throw new ToolchainCanceledException(aoce,
					new RunningTaskInfo(getClass(), "collecting reachable states of proof product"));
		}
		final var states = automatonReachableStates.getStates();
		final var listToIPredicate = new HashMap<List<IPredicate>, IPredicate>();
		for (final List<IPredicate> list : states) {
			listToIPredicate.put(list, mFactory.and(list));
		}
		return listToIPredicate;
	}

	private NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>> getEmpireAutomaton() {
		final var stateToPredicate = listStateToPredicate();
		final var lazyAutomaton = new ModularEmpireAutomaton<>(mProgram, mProofProduct, stateToPredicate, mServices);
		final NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>> automaton;
		mLogger.info("Exploring empire automaton...");
		try {
			automaton = new NestedWordAutomatonReachableStates<>(new AutomataLibraryServices(mServices), lazyAutomaton);
			mLogger.info("Explored empire automaton has %s", automaton.sizeInformation());
		} catch (final AutomataOperationCanceledException aoce) {
			throw new ToolchainCanceledException(aoce,
					new RunningTaskInfo(getClass(), "collecting reachable states of empire automaton"));
		}
		return automaton;
	}

	private boolean checkOwickiGriesValidity(final OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> annotation) {
		mStatistics.startOwickiGriesValidity();
		try {
			final var validity =
					new PetriOwickiGriesValidityCheck<>(mServices, mMgdScript, mProgram, mModifiableGlobals, annotation)
							.isValid();
			assert validity != Validity.INVALID : "Owicki-Gries annotation is invalid";
			if (validity == Validity.UNKNOWN) {
				mLogger.warn("Could not prove validity of Owicki-Gries annotation");
			}
			return validity != Validity.INVALID;
		} finally {
			mStatistics.stopOwickiGriesValidity();
		}
	}

	private INestedWordAutomaton<L, List<IPredicate>>
			convertPredicatesToList(final INestedWordAutomaton<L, IPredicate> interpolantAutomaton) {
		final var alphabet = new VpAlphabet<>(interpolantAutomaton.getAlphabet());
		final var convertedAutomaton = new NestedWordAutomaton<L, List<IPredicate>>(
				new AutomataLibraryServices(mServices), alphabet, List::of);
		// Assume there exists only one initial state by definition of empire automata
		final var initState =
				DataStructureUtils.getOneAndOnly(interpolantAutomaton.getInitialStates(), "initial state");
		final var queue = new ArrayDeque<List<IPredicate>>();
		final var visited = new HashSet<List<IPredicate>>();
		final var initList = List.of(initState);
		convertedAutomaton.addState(true, false, initList);
		queue.offer(initList);
		while (!queue.isEmpty()) {
			final var currentState = queue.poll();
			if (!visited.add(currentState)) {
				continue;
			}
			assert currentState.size() == 1 : "There is not exactly one state in the list";
			final var predicate = currentState.getFirst();
			final var successors = interpolantAutomaton.internalSuccessors(predicate);
			for (final OutgoingInternalTransition<L, IPredicate> succ : successors) {
				final var succState = succ.getSucc();
				final var transition = succ.getLetter();
				final var succList = List.of(succState);
				if (!convertedAutomaton.getStates().contains(succList)) {
					final var isFinal = interpolantAutomaton.isFinal(succState);
					convertedAutomaton.addState(false, isFinal, succList);
					queue.offer(succList);
				}
				convertedAutomaton.addInternalTransition(currentState, transition, succList);
			}
		}
		return convertedAutomaton;
	}

	@Override
	public void finalize(final IPetriNet<L, P> refinedNet, final BranchingProcess<L, P> refinedNetUnfolding) {
		mRefinedUnfolding = refinedNetUnfolding;
	}

	@Override
	public IPetriNet<L, P> getProgram() {
		return mProgram;
	}

	private LegalEmpireToOG<L, P> getOwickiGriesAnnotation(
			final IPossibleInterferences<Transition<L, P>, P> possibleInterferences,
			final NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>> empire,
			final LegalFocus<L, P> legalFocus) {
		return new LegalEmpireToOG<>(mServices, mMgdScript, mProgram, mSymbolTable, mProcedures, empire, legalFocus,
				possibleInterferences);
	}

	// Extending the LegalFocus class like this is a hack.
	// TODO Refactor focus so that different implementations of some common interface can be passed to this class.
	private static final class TrivialLegalFocus<L, P> extends LegalFocus<L, P> {
		public TrivialLegalFocus(final IPetriNet<L, P> net) {
			super(net);
		}

		@Override
		public Set<Region<P>> getLegalFocus(final State<L, P> state, final Integer lawIndex) {
			return state.territory().getRegions();
		}

		@Override
		public boolean isFocused(final P place, final State<L, P> state, final Integer lawIndex) {
			return state.territory().containsPlace(place);
		}

		@Override
		public List<IPredicate> getFocusedLaws(final State<L, P> state, final Region<P> region) {
			if (state.territory().getRegions().contains(region)) {
				return state.laws();
			}
			return List.of();
		}
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	private static final class Statistics extends OwickiGriesStatistics {
		private final TimeTracker mFocusTimer = new TimeTracker();

		public Statistics(final ILogger logger) {
			super(logger, EmpireComputation.class, EmpireToOwickiGries.class);
			declareTimeTracker("Focus computation time", mFocusTimer);
		}

		public void reportEmpire(final IStatisticsDataProvider statistics) {
			reportEmpireStatistics(statistics, null);
		}

		private void startFocusComputation() {
			mFocusTimer.start();
		}

		private void stopFocusComputation() {
			mFocusTimer.stop();
		}
	}

	private static final class ProofUnionFactory implements IUnionStateFactory<List<IPredicate>> {
		private final List<IPredicate> mEmptyStack;

		public ProofUnionFactory() {
			mEmptyStack = List.of();
		}

		@Override
		public List<IPredicate> createEmptyStackState() {
			return mEmptyStack;
		}

		@Override
		public List<IPredicate> createSinkStateContent() {
			throw new UnsupportedOperationException();
		}

		@Override
		public List<IPredicate> union(final List<IPredicate> state1, final List<IPredicate> state2) {
			return DataStructureUtils.concat(state1, state2);
		}
	}
}
