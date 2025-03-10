package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireAutomaton.State;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class EmpireAutomatonValidityCheck<PLACE, LETTER extends IAction> {
	private final ILogger mLogger;

	private final MonolithicHoareTripleChecker mHc;
	private final BasicPredicateFactory mFactory;

	private final EmpireAutomaton<LETTER, PLACE> mEmpireAutomaton;
	private final IPetriNet<LETTER, PLACE> mNet;
	private final Validity mValidity;

	public EmpireAutomatonValidityCheck(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final BasicPredicateFactory factory, final IPetriNet<LETTER, PLACE> net,
			final ModifiableGlobalsTable modifiableGlobals, final EmpireAutomaton<LETTER, PLACE> empire) {
		mLogger = services.getLoggingService().getLogger(EmpireValidityCheck.class);
		mHc = new MonolithicHoareTripleChecker(mgdScript, modifiableGlobals);
		mFactory = factory;

		mNet = net;
		mEmpireAutomaton = empire;

		mValidity = checkValidity();
	}

	private Validity checkValidity() {

		final var initialStates = mEmpireAutomaton.getInitialStates();
		final Set<State<LETTER, PLACE>> initialState = new HashSet<>();
		initialStates.forEach(initialState::add);
		if (checkInitialTerritories(initialState) != Validity.VALID) {
			return Validity.INVALID;
		}
		final var successorValidity = checkSuccessorValidity(initialState);
		if (successorValidity.getFirst() != Validity.VALID) {
			return Validity.INVALID;
		}
		if (checkAcceptingPlaces(successorValidity.getSecond()) != Validity.VALID) {
			return Validity.INVALID;
		}
		final var pairs = successorValidity.getSecond().stream().map(s -> new Pair<>(s.territory(), s.law()))
				.collect(Collectors.toSet());
		return Validity.VALID;
	}

	private Validity checkInitialTerritories(final Set<State<LETTER, PLACE>> initialState) {
		if (initialState.isEmpty()) {
			mLogger.warn("Empire annotation does not contain any initial Territory");
			return Validity.INVALID;
		}
		for (final State<LETTER, PLACE> state : initialState) {
			final var territory = state.territory();
			final var law = state.law();
			final var bystanders = state.bystanders();
			if (!territory.containsMarking(Marking.initial(mNet))) {
				mLogger.warn(
						"Initial State does not contain initial marking:\n\tterritory: %s \n\tlaw: %s \n\tbystanders: "
								+ "%s",
						territory, law, bystanders);
				return Validity.INVALID;
			}
			if (!SmtUtils.isTrueLiteral(law.getFormula())) {
				mLogger.warn("Initial State contains Law that does not evaluate to true:\n\tterritory: %s \n\tlaw: %s "
						+ "\n\tbystanders: %s", territory, law, bystanders);
				return Validity.INVALID;
			}
		}
		return Validity.VALID;
	}

	private Pair<Validity, Set<State<LETTER, PLACE>>>
			checkSuccessorValidity(final Set<State<LETTER, PLACE>> initialState) {
		final Set<State<LETTER, PLACE>> visitedStates = new HashSet<>();
		final var queue = new ArrayDeque<State<LETTER, PLACE>>();
		for (final State<LETTER, PLACE> state : initialState) {
			queue.offer(state);
		}
		while (!queue.isEmpty()) {
			final var state = queue.poll();
			if (!visitedStates.add(state)) {
				continue;
			}
			final var territory = state.territory();
			final var law = state.law();
			for (final var transition : (Iterable<Transition<LETTER, PLACE>>) territory
					.getEnabledTransitions(mNet)::iterator) {
				final var successorStates = mEmpireAutomaton.internalSuccessors(state, transition);
				final Set<State<LETTER, PLACE>> successorState = new HashSet<>();
				successorStates.forEach(i -> successorState.add(i.getSucc()));
				assert successorState.size() < 2 : "More then one successor";
				final Validity contradiction = checkContradiction(law, transition, territory);
				if (contradiction != Validity.VALID && successorState.isEmpty()) {
					mLogger.warn("The State:\n \t%s \n \thas no valid successor and does not evaluate to false with \n "
							+ "\ttransition %s", state, transition.getSymbol().getTransformula());
					return new Pair<>(Validity.INVALID, Collections.emptySet());
				}
				final var hoareValidity = checkHoareValidity(successorState, law, transition);
				if (!hoareValidity) {
					return new Pair<>(Validity.INVALID, Collections.emptySet());
				}
				final var isValidSuccessor = checkValidSuccessor(successorState, state, transition);
				if (!isValidSuccessor) {
					return new Pair<>(Validity.INVALID, Collections.emptySet());
				}
				for (final var succ : successorState) {
					queue.offer(succ);
				}
			}
		}
		return new Pair<>(Validity.VALID, visitedStates);
	}

	private Validity checkAcceptingPlaces(final Set<State<LETTER, PLACE>> states) {
		final var accepting = mNet.getAcceptingPlaces();
		for (final State<LETTER, PLACE> state : states) {
			final var territory = state.territory();
			final var law = state.law();
			if (DataStructureUtils.haveNonEmptyIntersection(territory.getPlaces(), accepting)
					&& !SmtUtils.isFalseLiteral(law.getFormula())) {
				return Validity.INVALID;
			}
		}
		return Validity.VALID;
	}

	private boolean checkHoareTriple(final IPredicate pre, final IPredicate post,
			final Transition<LETTER, PLACE> transition) {
		final var valid = mHc.checkInternal(pre, (IInternalAction) transition.getSymbol(), post);
		return valid == Validity.VALID;
	}

	private Validity checkContradiction(final IPredicate lawConjunction, final Transition<LETTER, PLACE> transition,
			final Territory<PLACE> territory) {
		if (!checkHoareTriple(lawConjunction, mFactory.or(), transition)) {
			return Validity.INVALID;
		}
		return Validity.VALID;
	}

	private boolean checkHoareValidity(final Set<State<LETTER, PLACE>> successorState, final IPredicate law,
			final Transition<LETTER, PLACE> transition) {
		for (final State<LETTER, PLACE> state : successorState) {
			final var successorLaw = state.law();
			final var valid = checkHoareTriple(law, successorLaw, transition);
			if (!valid) {
				mLogger.warn("Invalid Hoare Triple\n \tprecondition %s \taction %s \tpostcondition %s", law,
						transition.getSymbol().getTransformula(), successorLaw);
				return false;
			}
		}
		return true;
	}

	private boolean checkValidSuccessor(final Set<State<LETTER, PLACE>> successorState,
			final State<LETTER, PLACE> predState, final Transition<LETTER, PLACE> transition) {
		final var territory = predState.territory();
		for (final State<LETTER, PLACE> state : successorState) {
			if (!territory.isSuccessor(state.territory(), transition)) {
				return false;
			}
		}
		return true;
	}

	public Validity getValidity() {
		return mValidity;
	}
}
