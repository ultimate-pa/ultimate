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

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.TotalizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
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
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.DirectedEmpireAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.DirectedEmpireAutomaton.State;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.DirectedEmpireProduct;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.DirectedEmpireProduct.ProductState;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.DirectedLegalEmpireToOG;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.DirectedLegalFocus;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.TimeTracker;

public class DirectedLegalFocusOwickiGries<L extends IAction, P> implements IPetriNetProofProducer<L, P> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final IPetriNet<L, P> mProgram;
	private final ManagedScript mMgdScript;
	private final IIcfgSymbolTable mSymbolTable;
	private final Set<String> mProcedures;
	private final ModifiableGlobalsTable mModifiableGlobals;

	private final Statistics mStatistics;

	private final List<INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> mProofs = new ArrayList<>();
	private IPossibleInterferences<Transition<L, P>, P> mPossibleInterferences;

	private OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> mOwickiGries;
	private INwaOutgoingLetterAndTransitionProvider<Transition<L, P>, ProductState<L, P>> mProduct;

	public DirectedLegalFocusOwickiGries(final IUltimateServiceProvider services, final IPetriNet<L, P> program,
			final CfgSmtToolkit csToolkit) {
		this(services, program, csToolkit.getManagedScript(), csToolkit.getSymbolTable(), csToolkit.getProcedures(),
				csToolkit.getModifiableGlobalsTable());
	}

	public DirectedLegalFocusOwickiGries(final IUltimateServiceProvider services, final IPetriNet<L, P> program,
			final ManagedScript mgdScript, final IIcfgSymbolTable symbolTable, final Set<String> procedures,
			final ModifiableGlobalsTable modifiableGlobals) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(getClass());
		mProgram = program;
		mMgdScript = mgdScript;
		mSymbolTable = symbolTable;
		mProcedures = procedures;
		mModifiableGlobals = modifiableGlobals;
		mStatistics = new Statistics(mLogger);
	}

	@Override
	public void initialize(final IPossibleInterferences<Transition<L, P>, P> possibleInterferences) {
		mPossibleInterferences = possibleInterferences;
	}

	@Override
	public void refine(final IPredicateUnifier unifier, final INestedWordAutomaton<L, IPredicate> interpolantAutomaton,
			final Map<Transition<L, P>, Transition<L, P>> transitionBacktranslation) {
		assert mPossibleInterferences != null : getClass().getSimpleName() + " was not initialized";

		final var initialTrueState =
				DataStructureUtils.getOneAndOnly(interpolantAutomaton.getInitialStates(), "initial state");
		final var totalizedProof = new TotalizeNwa<>(interpolantAutomaton, initialTrueState, false);
		mProofs.add(totalizedProof);
	}

	@Override
	public boolean isReadyToComputeProof() {
		return true;
	}

	@Override
	public OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> getOrComputeProof() {
		final List<NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>>> empireAutomata;
		mStatistics.startEmpireComputation();
		try {
			empireAutomata = getEmpireAutomata();
			mProduct = constructProduct(empireAutomata);
		} finally {
			mStatistics.stopEmpireComputation();
		}

		final DirectedLegalFocus<L, P> legalFocus;
		mStatistics.startFocusComputation();
		try {
			mLogger.info("Computing focus for %d empire automata", empireAutomata.size());
			legalFocus = new DirectedLegalFocus<>(new HashSet<>(empireAutomata), mProgram);
		} finally {
			mStatistics.stopFocusComputation();
		}

		mStatistics.startOwickiGriesComputation();
		try {
			final var annotationConstruction = getOwickiGriesAnnotation(mPossibleInterferences, legalFocus);
			mOwickiGries = annotationConstruction.getAnnotation();
		} finally {
			mStatistics.stopOwickiGriesComputation();
		}

		assert checkOwickiGriesValidity(mOwickiGries) : "Owicki Gries annotation is invalid";
		return mOwickiGries;
	}

	private INestedWordAutomaton<Transition<L, P>, ProductState<L, P>>
			constructProduct(final List<NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>>> automata) {
		final var productConstruction = new DirectedEmpireProduct<>(automata, mProgram, mServices);
		return productConstruction.getProductAutomaton();
	}

	private List<NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>>> getEmpireAutomata() {
		final var lazyAutomata =
				mProofs.stream().map(proof -> new DirectedEmpireAutomaton<L, P>(mProgram, proof, mServices))
						.collect(Collectors.toList());
		final var automata = new ArrayList<NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>>>();
		for (final DirectedEmpireAutomaton<L, P> empireAutomaton : lazyAutomata) {
			mLogger.info("Exploring empire automaton...");
			try {
				final var automaton = new NestedWordAutomatonReachableStates<>(new AutomataLibraryServices(mServices),
						empireAutomaton);
				automata.add(automaton);
				mLogger.info("Explored empire automaton has %s", automaton.sizeInformation());
			} catch (final AutomataOperationCanceledException aoce) {
				throw new ToolchainCanceledException(aoce,
						new RunningTaskInfo(getClass(), "collecting reachable states of empire automaton"));
			}
		}
		return automata;
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

	@Override
	public void finalize(final IPetriNetSuccessorProvider<L, P> refinedNet,
			final BranchingProcess<L, P> refinedNetUnfolding) {
		// nothing to do here
	}

	@Override
	public IPetriNet<L, P> getProgram() {
		return mProgram;
	}

	private DirectedLegalEmpireToOG<L, P> getOwickiGriesAnnotation(
			final IPossibleInterferences<Transition<L, P>, P> possibleInterferences,
			final DirectedLegalFocus<L, P> legalFocus) {
		return new DirectedLegalEmpireToOG<>(mServices, mMgdScript, mProgram, mSymbolTable, mProcedures, mProduct,
				legalFocus, possibleInterferences);
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	private static final class Statistics extends OwickiGriesStatistics {
		private final TimeTracker mFocusTimer = new TimeTracker();

		public Statistics(final ILogger logger) {
			super(logger, DirectedEmpireAutomaton.class, DirectedLegalEmpireToOG.class);
			declareTimeTracker("Focus computation time", mFocusTimer);
		}

		private void startFocusComputation() {
			mFocusTimer.start();
		}

		private void stopFocusComputation() {
			mFocusTimer.stop();
		}
	}

	private static final class UnionFactory<L, P> implements IUnionStateFactory<List<State<L, P>>> {
		private final List<State<L, P>> mEmptyStack;

		public UnionFactory() {
			mEmptyStack = List.of();
		}

		@Override
		public List<State<L, P>> createEmptyStackState() {
			return mEmptyStack;
		}

		@Override
		public List<State<L, P>> union(final List<State<L, P>> state1, final List<State<L, P>> state2) {
			return DataStructureUtils.concat(state1, state2);
		}

		@Override
		public List<State<L, P>> createSinkStateContent() {
			throw new UnsupportedOperationException();
		}
	}
}
