package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire;

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class ModularEmpireAutomaton<L, P> implements IEmpireAutomaton<L, P, ModularEmpireAutomaton.State<L, P>> {
	private final ILogger mLogger;

	private final IPetriNet<L, P> mNet;
	private final INwaOutgoingLetterAndTransitionProvider<L, List<IPredicate>> mProduct;
	private final Map<List<IPredicate>, IPredicate> mListToPredicate;

	private final State<L, P> mInitialState;

	public ModularEmpireAutomaton(final IPetriNet<L, P> net,
			final INwaOutgoingLetterAndTransitionProvider<L, List<IPredicate>> product,
			final Map<List<IPredicate>, IPredicate> listPredicateMap, final IUltimateServiceProvider services) {
		mLogger = services.getLoggingService().getLogger(getClass());
		mNet = net;
		mProduct = product;
		mListToPredicate = listPredicateMap;

		// Construct initial state
		final var initialLaw = DataStructureUtils.getOneAndOnly(mProduct.getInitialStates(), "initial law place");
		final var regions = mNet.getInitialPlaces().stream().map(Region::singleton).collect(ImmutableSet.collector());
		final State<L, P> state = new State<>(new Territory<>(regions), initialLaw, Collections.emptySet());
		mInitialState = getMarkedSuccessor(state);
	}

	@Override
	public IPredicate getLaw(final State<L, P> state) {
		return mListToPredicate.get(state.laws());
	}

	@Override
	public boolean containsPlace(final State<L, P> state, final P place) {
		return state.territory().containsPlace(place);
	}

	@Override
	public VpAlphabet<Transition<L, P>> getVpAlphabet() {
		return new VpAlphabet<>(mNet.getTransitions());
	}

	@Override
	public Iterable<State<L, P>> getInitialStates() {
		return List.of(mInitialState);
	}

	@Override
	public boolean isInitial(final State<L, P> state) {
		return mInitialState.equals(state);
	}

	/**
	 * Determines a state s as final, if it contains an error place and the law is false, OR if there exists at least
	 * one transition in enabled(territory(s)), for which there is no successor in the automaton. In this case, the
	 * successor law must be false.
	 */
	@Override
	public boolean isFinal(final State<L, P> state) {
		final var territory = state.territory();
		final var enabledTransitions = territory.getEnabledTransitions(mNet).collect(Collectors.toSet());
		for (final Transition<L, P> transition : enabledTransitions) {
			final var succ = internalSuccessors(state, transition);
			if (!succ.iterator().hasNext()) {
				assert SmtUtils
						.isFalseLiteral(mListToPredicate.get(getSuccessorLaw(state.laws(), transition)).getFormula())
						: "There is no successor, but the law is not false";
				return true;
			}
		}
		return false;
	}

	@Override
	public int size() {
		return -1;
	}

	@Override
	public String sizeInformation() {
		return "unknown size";
	}

	@Override
	public Set<Transition<L, P>> lettersInternal(final State<L, P> state) {
		// TODO Consider whether we can efficiently override this method
		return IEmpireAutomaton.super.lettersInternal(state);
	}

	@Override
	public Iterable<OutgoingInternalTransition<Transition<L, P>, State<L, P>>>
			internalSuccessors(final State<L, P> state, final Transition<L, P> letter) {
		// step 1: see if letter should lead to any successor at all or can be optimized away
		// (iterate over alphabet and see which other transitions are enabled in the territory)
		if (!state.territory().enables(letter)) {
			return List.of();
		}
		if (isExtendingTransition(state.laws(), letter) && isCycle(state, letter)) {
			return List.of(new OutgoingInternalTransition<>(letter, state));
		}

		// step 2: compute the "direct" successor state for the given transition
		final var directSucc = getReplacementSuccessor(state, letter);
		final var succLaw = directSucc.laws();
		if (SmtUtils.isFalseLiteral(mListToPredicate.get(succLaw).getFormula())) {
			return List.of();
		}

		// step 3: while the current successor is not marked, pick one (or a set of) transitions and compute the
		// successor again
		final var maxMarkedSuccessor = getMarkedSuccessor(directSucc);

		// return the edge to the maximal successor
		return List.of(new OutgoingInternalTransition<>(letter, maxMarkedSuccessor));
	}

	private State<L, P> extendAll(final State<L, P> state, final Set<Transition<L, P>> transitions) {
		if (transitions.isEmpty()) {
			return state;
		}
		final var territory = state.territory;
		final var territoryRegions = new HashSet<>(territory.getRegions());
		final var extendedRegions = new HashSet<Region<P>>();
		for (final Region<P> region : territory.getRegions()) {
			final var matchingTransitions = findMatchingTransitions(region, transitions);
			if (!matchingTransitions.isEmpty()) {
				transitions.removeAll(matchingTransitions);
				final var successorPlaces = matchingTransitions.stream().flatMap(t -> t.getSuccessors().stream())
						.collect(Collectors.toSet());
				extendedRegions.add(
						new Region<>(ImmutableSet.of(DataStructureUtils.union(region.getPlaces(), successorPlaces))));
				territoryRegions.remove(region);
			}
		}
		final var newTerritory =
				new Territory<>(ImmutableSet.of(DataStructureUtils.union(extendedRegions, territoryRegions)));
		return new State<>(newTerritory, state.laws(), state.bystanders);
	}

	private Set<Transition<L, P>> findMatchingTransitions(final Region<P> region,
			final Set<Transition<L, P>> transitions) {
		final var predTransitions = new HashSet<Transition<L, P>>();
		final var places = region.getPlaces();
		for (final Transition<L, P> transition : transitions) {
			if (places.containsAll(transition.getPredecessors())) {
				predTransitions.add(transition);
			}
		}
		return predTransitions;
	}

	private Set<Transition<L, P>> getEnabledTransitions(final State<L, P> state) {
		return state.territory().getEnabledTransitions(mNet)
				.filter(transition -> !SmtUtils
						.isFalseLiteral(mListToPredicate.get(getSuccessorLaw(state.laws(), transition)).getFormula()))
				.collect(Collectors.toSet());
	}

	private List<IPredicate> getSuccessorLaw(final List<IPredicate> laws, final Transition<L, P> transition) {
		final var succLaw = mProduct.internalSuccessors(laws, transition.getSymbol());
		if (!succLaw.iterator().hasNext()) {
			return laws;
		}
		return DataStructureUtils.getOneAndOnly(succLaw, "successor state").getSucc();
	}

	private boolean isExtendingTransition(final List<IPredicate> laws, final Transition<L, P> transition) {
		final List<IPredicate> newLaw = getSuccessorLaw(laws, transition);
		final var predecessors = transition.getPredecessors();
		final var successors = transition.getSuccessors();
		return mListToPredicate.get(laws) == mListToPredicate.get(newLaw) && predecessors.size() == 1
				&& successors.size() == 1;
	}

	private Set<Transition<L, P>> getExtendingTransitions(final State<L, P> state,
			final Set<Transition<L, P>> transitions) {
		return transitions.stream().filter(transition -> isExtendingTransition(state.laws(), transition))
				.collect(Collectors.toSet());
	}

	private boolean isNecessaryBridge(final State<L, P> state, final Transition<L, P> transition) {
		return !state.territory.getBystanders(transition).containsAll(state.bystanders);
	}

	private Set<Transition<L, P>> getUnnecessaryTransitions(final State<L, P> state,
			final Set<Transition<L, P>> transitions) {
		final var extending = getExtendingTransitions(state, transitions);
		return extending.stream().filter(t -> !isNecessaryBridge(state, t)).collect(Collectors.toSet());
	}

	private boolean isCycle(final State<L, P> state, final Transition<L, P> transition) {
		final var territory = state.territory;
		final var laws = state.laws();
		if (!territory.enables(transition) || !isExtendingTransition(laws, transition)) {
			return false;
		}
		return territory.getPlaces().containsAll(transition.getSuccessors());
	}

	private State<L, P> getMarkedSuccessor(final State<L, P> state) {
		final var enabledTransitions = getEnabledTransitions(state);
		final var unnecessaryTransitions = getUnnecessaryTransitions(state, enabledTransitions);
		final var nonCyclicTransitions =
				unnecessaryTransitions.stream().filter(t -> !isCycle(state, t)).collect(Collectors.toSet());
		if (nonCyclicTransitions.isEmpty()) {
			return state;
		}
		final var extendedState = extendAll(state, nonCyclicTransitions);
		return getMarkedSuccessor(extendedState);
	}

	private State<L, P> getReplacementSuccessor(final State<L, P> state, final Transition<L, P> transition) {
		final List<IPredicate> newLawPlace = getSuccessorLaw(state.laws(), transition);
		final Set<Region<P>> newBystanders = state.territory().getBystanders(transition);
		final var regions = replaceRegions(transition, newBystanders);
		final var newTerritory = new Territory<>(ImmutableSet.of(regions));
		return new State<>(newTerritory, newLawPlace, newBystanders);
	}

	private Set<Region<P>> replaceRegions(final Transition<L, P> transition, final Set<Region<P>> bystanders) {
		final var regions = new HashSet<>(bystanders);
		for (final var succ : transition.getSuccessors()) {
			regions.add(Region.singleton(succ));
		}
		return regions;
	}

	// TODO use ImmutableSet for bystanders
	public record State<L, P>(Territory<P, Region<P>> territory, List<IPredicate> laws, Set<Region<P>> bystanders,
			int hash) {
		// Convenience constructor that computes the correct hash code. Always use this constructor.
		public State(final Territory<P, Region<P>> territory, final List<IPredicate> laws,
				final Set<Region<P>> bystanders) {
			this(territory, laws, bystanders, Objects.hash(territory, laws, bystanders));
		}

		@Override
		public int hashCode() {
			// Hash code is cached for performance.
			// TODO This caching is brittle, as accidental constructor misuse can lead to incorrect hash codes.
			// TODO Re-evaluate the impact other implementation details have been improved, and improve or remove it.
			return hash;
		}
	}
}
