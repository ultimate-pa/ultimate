package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

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
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireAutomaton.State;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireComputation;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireToOwickiGries;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.LegalEmpireToOG;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.LegalFocus;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.PetriOwickiGries;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

public class LegalFocusOwickiGries<L extends IAction, P> implements IPetriNetProofProducer<L, P> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final IPetriNet<L, P> mProgram;
	private final ManagedScript mMgdScript;
	private final IIcfgSymbolTable mSymbolTable;
	private final Set<String> mProcedures;
	private final ModifiableGlobalsTable mModifiableGlobals;
	private BranchingProcess<L, P> mRefinedUnfolding;

	private final Statistics mStatistics;
	private final IUnionStateFactory<List<State<L, P>>> mUnionFactory;

	private Function<Transition<L, P>, Transition<L, P>> mDiff2OriginalTransition = Function.identity();
	private final List<INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> mProofs = new ArrayList<>();
	private OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> mOwickiGries;
	private INwaOutgoingLetterAndTransitionProvider<Transition<L, P>, List<State<L, P>>> mProduct = null;

	public LegalFocusOwickiGries(final IUltimateServiceProvider services, final IPetriNet<L, P> program,
			final CfgSmtToolkit csToolkit) {
		this(services, program, csToolkit.getManagedScript(), csToolkit.getSymbolTable(), csToolkit.getProcedures(),
				csToolkit.getModifiableGlobalsTable());
	}

	public LegalFocusOwickiGries(final IUltimateServiceProvider services, final IPetriNet<L, P> program,
			final ManagedScript mgdScript, final IIcfgSymbolTable symbolTable, final Set<String> procedures,
			final ModifiableGlobalsTable modifiableGlobals) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(getClass());
		mProgram = program;
		mMgdScript = mgdScript;
		mSymbolTable = symbolTable;
		mProcedures = procedures;
		mModifiableGlobals = modifiableGlobals;
		mUnionFactory = new UnionFactory();
		mStatistics = new Statistics(mLogger);
	}

	@Override
	public void refine(final IPredicateUnifier unifier, final INestedWordAutomaton<L, IPredicate> interpolantAutomaton,
			final Map<Transition<L, P>, Transition<L, P>> transitionBacktranslation) {
		mDiff2OriginalTransition = mDiff2OriginalTransition.compose(transitionBacktranslation::get);

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
		final var possibleInterferences = PetriOwickiGries.getPossibleInterferences(mRefinedUnfolding,
				mProgram.getPlaces(), mDiff2OriginalTransition);

		mStatistics.startEmpireComputation();
		final var empireAutomata = getEmpireAutomata();
		final var legalFocus = new LegalFocus<>(empireAutomata, mProgram);
		final var listStateEmpires = convertEmpires(empireAutomata);
		constructProduct(listStateEmpires);
		mStatistics.stopEmpireComputation();

		mStatistics.startOwickiGriesComputation();
		final var annotationConstruction = getOwickiGriesAnnotation(possibleInterferences, legalFocus);
		mOwickiGries = annotationConstruction.getAnnotation();
		mStatistics.stopOwickiGriesComputation();
		assert checkOwickiGriesValidity(mOwickiGries) : "Owicki Gries annotation is invalid";
		return mOwickiGries;
	}

	private void constructProduct(final List<INestedWordAutomaton<Transition<L, P>, List<State<L, P>>>> automatons) {
		for (final INestedWordAutomaton<Transition<L, P>, List<State<L, P>>> iNestedWordAutomaton : automatons) {
			addToProduct(iNestedWordAutomaton);
		}
	}

	private void addToProduct(final INestedWordAutomaton<Transition<L, P>, List<State<L, P>>> automaton) {
		if (mProduct == null) {
			mProduct = automaton;
		}
		try {
			mProduct = new UnionNwa<>(mProduct, automaton, mUnionFactory, false);
		} catch (final AutomataLibraryException e) {
			throw new AssertionError(e);
		}
	}

	private Set<NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>>> getEmpireAutomata() {
		final var lazyAutomata = mProofs.stream().map(proof -> new EmpireAutomaton<L, P>(mProgram, proof, mServices))
				.collect(Collectors.toSet());
		final var automata = new HashSet<NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>>>();
		for (final EmpireAutomaton<L, P> empireAutomaton : lazyAutomata) {
			try {
				final var automaton = new NestedWordAutomatonReachableStates<>(new AutomataLibraryServices(mServices),
						empireAutomaton);
				automata.add(automaton);
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

	private List<INestedWordAutomaton<Transition<L, P>, List<State<L, P>>>>
			convertEmpires(final Set<NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>>> empires) {
		final var convertedEmpires = new ArrayList<INestedWordAutomaton<Transition<L, P>, List<State<L, P>>>>();
		for (final NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>> nestedWordAutomaton : empires) {
			final var convertedEmpire = convertStatesToList(nestedWordAutomaton);
			convertedEmpires.add(convertedEmpire);
		}
		return convertedEmpires;
	}

	private INestedWordAutomaton<Transition<L, P>, List<State<L, P>>>
			convertStatesToList(final NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>> empire) {
		final var alphabet = new VpAlphabet<>(mProgram.getTransitions());
		final var convertedEmpire = new NestedWordAutomaton<Transition<L, P>, List<State<L, P>>>(
				new AutomataLibraryServices(mServices), alphabet, List::of);
		// Assume there exists only one initial state by definition of empire automata
		final var initState = DataStructureUtils.getOneAndOnly(empire.getInitialStates(), "initial state");
		final var queue = new ArrayDeque<List<State<L, P>>>();
		final var visited = new HashSet<List<State<L, P>>>();
		final var initList = List.of(initState);
		convertedEmpire.addState(true, false, initList);
		queue.offer(initList);
		while (!queue.isEmpty()) {
			final var currentState = queue.poll();
			if (!visited.add(currentState)) {
				continue;
			}
			assert currentState.size() == 1 : "There is not exactly one state in the list";
			final var state = currentState.getFirst();
			final var successors = empire.internalSuccessors(state);
			for (final OutgoingInternalTransition<Transition<L, P>, State<L, P>> succ : successors) {
				final var succState = succ.getSucc();
				final var transition = succ.getLetter();
				final var succList = List.of(succState);
				if (!convertedEmpire.getStates().contains(succList)) {
					convertedEmpire.addState(false, false, succList);
					queue.offer(succList);
				}
				convertedEmpire.addInternalTransition(currentState, transition, succList);
			}
		}
		return convertedEmpire;
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
			final LegalFocus<L, P> legalFocus) {
		return new LegalEmpireToOG<>(mServices, mMgdScript, mProgram, mSymbolTable, mProcedures, mProduct, legalFocus,
				possibleInterferences);
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	private static final class Statistics extends OwickiGriesStatistics {
		public Statistics(final ILogger logger) {
			super(logger, EmpireComputation.class, EmpireToOwickiGries.class);
		}

		public void reportEmpire(final IStatisticsDataProvider statistics) {
			reportEmpireStatistics(statistics, null);
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
