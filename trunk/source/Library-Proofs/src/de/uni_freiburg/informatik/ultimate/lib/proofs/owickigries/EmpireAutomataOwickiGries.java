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

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.TotalizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.UnionNwa;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IUnionStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateWithConjuncts;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireAutomataStatistics;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireAutomaton.State;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireAutomatonValidityCheck;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireReachableStates;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireToOwickiGries;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.IExplicitEmpireAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.ILegalFocusFunction;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.LegalFocus;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.TimeTracker;

public class EmpireAutomataOwickiGries<L extends IAction, P> implements IPetriNetProofProducer<L, P> {
	public enum FocusComputation {
		UNFOCUSED, GLOBAL, MODULAR
	}

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	private final IPetriNet<L, P> mProgram;
	private final ManagedScript mMgdScript;
	private final IIcfgSymbolTable mSymbolTable;
	private final Set<String> mProcedures;
	private final ModifiableGlobalsTable mModifiableGlobals;

	private final BasicPredicateFactory mFactory;
	private final FocusComputation mFocusComputation;

	private final ConjunctiveUnionFactory mProofUnionFactory;

	private IPossibleInterferences<Transition<L, P>, P> mPossibleInterferences;
	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mProofProduct;
	private int mNumProofs = 0;

	private OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> mOwickiGries;
	private final Statistics mStatistics;

	public EmpireAutomataOwickiGries(final IUltimateServiceProvider services, final IPetriNet<L, P> program,
			final CfgSmtToolkit csToolkit, final PredicateFactory factory, final FocusComputation focusComputation) {
		this(services, program, csToolkit.getManagedScript(), csToolkit.getSymbolTable(), csToolkit.getProcedures(),
				csToolkit.getModifiableGlobalsTable(), factory, focusComputation);
	}

	public EmpireAutomataOwickiGries(final IUltimateServiceProvider services, final IPetriNet<L, P> program,
			final ManagedScript mgdScript, final IIcfgSymbolTable symbolTable, final Set<String> procedures,
			final ModifiableGlobalsTable modifiableGlobals, final PredicateFactory factory,
			final FocusComputation focusComputation) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(getClass());

		mProgram = program;
		mMgdScript = mgdScript;
		mSymbolTable = symbolTable;
		mProcedures = procedures;
		mModifiableGlobals = modifiableGlobals;

		mFactory = factory;
		mFocusComputation = focusComputation;

		mProofUnionFactory = new ConjunctiveUnionFactory(factory);

		mStatistics = new Statistics(mLogger);
	}

	@Override
	public void initialize(final IPossibleInterferences<Transition<L, P>, P> possibleInterferences) {
		assert mPossibleInterferences == null : "already initialized";
		assert possibleInterferences != null : "did not provide possible interferences";

		mPossibleInterferences = possibleInterferences;
	}

	@Override
	public void refine(final IPredicateUnifier unifier, final INestedWordAutomaton<L, IPredicate> interpolantAutomaton,
			final Map<Transition<L, P>, Transition<L, P>> transitionBacktranslation) {
		assert mPossibleInterferences != null : getClass().getSimpleName() + " was not initialized";

		mNumProofs++;
		final var initialTrueState =
				DataStructureUtils.getOneAndOnly(interpolantAutomaton.getInitialStates(), "initial state");
		final var totalizedProof = new TotalizeNwa<>(interpolantAutomaton, initialTrueState, false);

		if (mProofProduct == null) {
			mProofProduct = totalizedProof;
		} else {
			try {
				mProofProduct = new UnionNwa<>(mProofProduct, totalizedProof, mProofUnionFactory, false);
			} catch (final AutomataLibraryException e) {
				throw new RuntimeException("Failed to compute union of proof automata", e);
			}
		}
	}

	@Override
	public boolean isReadyToComputeProof() {
		return true;
	}

	@Override
	public OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> getOrComputeProof() {
		if (mOwickiGries != null) {
			// If the proof was already computed, just return it.
			return mOwickiGries;
		}

		assert isReadyToComputeProof() : "Not ready to compute proof";

		final IExplicitEmpireAutomaton<L, P, State<L, P>> empireAutomaton = computeEmpireAutomaton();
		assert checkAutomatonValidity(empireAutomaton) : "Empire automaton is invalid";

		final ILegalFocusFunction<State<L, P>, P> legalFocus = computeFocus(empireAutomaton);

		mOwickiGries = computeOwickiGriesAnnotation(empireAutomaton, legalFocus);
		assert checkOwickiGriesValidity(mOwickiGries) : "Owicki Gries annotation is invalid";

		return mOwickiGries;
	}

	private IExplicitEmpireAutomaton<L, P, State<L, P>> computeEmpireAutomaton() {
		mStatistics.startEmpireComputation();
		try {
			final var lazyAutomaton = new EmpireAutomaton<>(mProgram, mProofProduct, mServices);

			mLogger.info("Exploring empire automaton...");
			final var automaton = new EmpireReachableStates<>(mServices, lazyAutomaton);

			mLogger.info("Explored empire automaton has %s", automaton.sizeInformation());
			mStatistics.reportEmpire(automaton);

			return automaton;
		} finally {
			mStatistics.stopEmpireComputation();
		}
	}

	private boolean checkAutomatonValidity(final IExplicitEmpireAutomaton<L, P, ?> automaton) {
		mLogger.info("Checking validity of empire automaton...");
		mStatistics.startEmpireValidity();
		try {
			final var checker = new EmpireAutomatonValidityCheck<>(mServices, mMgdScript, mFactory, mProgram,
					mModifiableGlobals, automaton);
			return checker.getValidity() != Validity.INVALID;
		} finally {
			mStatistics.stopEmpireValidity();
		}
	}

	private ILegalFocusFunction<State<L, P>, P>
			computeFocus(final IExplicitEmpireAutomaton<L, P, State<L, P>> empireAutomaton) {
		mLogger.info("Computing focus ...");
		mStatistics.startFocusComputation();
		try {
			return switch (mFocusComputation) {
			case UNFOCUSED -> new ILegalFocusFunction.TrivialFocus<>(empireAutomaton);
			case MODULAR -> new LegalFocus<>(empireAutomaton, mProgram, mProofProduct, mNumProofs,
					mProofUnionFactory::splitConjuncts);
			case GLOBAL -> new LegalFocus<>(empireAutomaton, mProgram, mProofProduct, 1, List::of);
			};
		} finally {
			mStatistics.stopFocusComputation();
		}
	}

	private OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> computeOwickiGriesAnnotation(
			final IExplicitEmpireAutomaton<L, P, State<L, P>> empire,
			final ILegalFocusFunction<State<L, P>, P> legalFocus) {
		mLogger.info("Converting empire automaton to Owicki-Gries annotation...");
		mStatistics.startOwickiGriesComputation();
		try {
			final var construction = new EmpireToOwickiGries<>(mServices, mMgdScript, mProgram, mSymbolTable,
					mProcedures, empire, mPossibleInterferences, legalFocus);
			return construction.getAnnotation();
		} finally {
			mStatistics.stopOwickiGriesComputation();
		}
	}

	private boolean checkOwickiGriesValidity(final OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> annotation) {
		mLogger.info("Checking validity of Owicki-Gries annotation...");
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
	public void finalize(final IPetriNetSuccessorProvider<L, P> refinedNet) {
		// Nothing to do here
	}

	@Override
	public IPetriNet<L, P> getProgram() {
		return mProgram;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	private static final class Statistics extends OwickiGriesStatistics {
		private final TimeTracker mFocusTimer = new TimeTracker();

		public Statistics(final ILogger logger) {
			super(logger, EmpireAutomaton.class, EmpireToOwickiGries.class);
			declareTimeTracker("Focus computation time", mFocusTimer);
		}

		public void reportEmpire(final IExplicitEmpireAutomaton<?, ?, ?> empire) {
			reportEmpireStatistics(new EmpireAutomataStatistics(empire));
		}

		private void startFocusComputation() {
			mFocusTimer.start();
		}

		private void stopFocusComputation() {
			mFocusTimer.stop();
		}
	}

	private static final class ConjunctiveUnionFactory implements IUnionStateFactory<IPredicate> {
		private final BasicPredicateFactory mFactory;

		public ConjunctiveUnionFactory(final BasicPredicateFactory factory) {
			mFactory = factory;
		}

		@Override
		public IPredicate createEmptyStackState() {
			return null;
		}

		@Override
		public IPredicate createSinkStateContent() {
			throw new UnsupportedOperationException("Cannot create sink state. Expecting total automata.");
		}

		@Override
		public IPredicate union(final IPredicate state1, final IPredicate state2) {
			return mFactory.construct(id -> new PredicateWithConjuncts(id, state1, state2));
		}

		public List<IPredicate> splitConjuncts(final IPredicate predicate) {
			if (predicate instanceof final PredicateWithConjuncts conjunction) {
				return conjunction.getConjuncts();
			}
			return List.of(predicate);
		}
	}
}
