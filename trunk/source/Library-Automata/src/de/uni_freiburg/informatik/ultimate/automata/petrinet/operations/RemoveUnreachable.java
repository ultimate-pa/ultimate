package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.HashSet;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEquivalent;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.FinitePrefix;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.SetOperations;

/**
 * Removes parts of a Petri Net that do not change its behavior.
 * <p>
 * A transition is unreachable iff it can never fire
 * (because there is no reachable marking covering all of its preceding places).
 * <p>
 * A place is unreachable iff it is not covered by any reachable marking.
 * <p>
 * This operation may also remove some of the reachable places if they are not needed.
 * Required are only
 * <ul>
 *   <li> places with a reachable successor transition,
 *   <li> or accepting-places with a reachable predecessor transition,
 *   <li> or at most one accepting initial place without a reachable successor transition.
 * </ul>
 * 
 * @author schaetzc@tf.uni-freiburg.de
 *
 * @param <LETTER>
 *            Type of letters in alphabet of Petri net
 * @param <PLACE>
 *            Type of places in Petri net
 * @param <CRSF>
 *            Type of factory needed to check the result of this operation in {@link #checkResult(CRSF)}
 */
public class RemoveUnreachable<LETTER, PLACE, CRSF extends
		IStateFactory<PLACE> & IPetriNet2FiniteAutomatonStateFactory<PLACE> & INwaInclusionStateFactory<PLACE>>
		extends UnaryNetOperation<LETTER, PLACE, CRSF> {

	private final BoundedPetriNet<LETTER, PLACE> mOperand;
	
	/** {@link #mOperand} with only reachable transitions and required places. */
	private final BoundedPetriNet<LETTER, PLACE> mResult;
	
	private final Set<ITransition<LETTER, PLACE>> mReachableTransitions;
	
	public RemoveUnreachable(AutomataLibraryServices services, BoundedPetriNet<LETTER, PLACE> operand)
			throws AutomataOperationCanceledException {
		this(services, operand, null);
	}
	
	/**
	 * @param operand
	 *     Petri net to be copied such that only reachable transitions remain.
	 * @param reachableTransitions
	 *     The reachable transitions (or a superset) of {@code operand}.
	 *     Can be computed from an existing finite prefix using {@link #reachableTransitions(BranchingProcess)}.
	 */
	public RemoveUnreachable(AutomataLibraryServices services, BoundedPetriNet<LETTER, PLACE> operand,
			Set<ITransition<LETTER, PLACE>> reachableTransitions) throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		mResult = new BoundedPetriNet<>(services, operand.getAlphabet(), operand.constantTokenAmount());
		mReachableTransitions = reachableTransitions == null ? reachableTransitions() : reachableTransitions;
		rebuildNetWithoutDeadNodes();
	}

	private Set<ITransition<LETTER, PLACE>> reachableTransitions() throws AutomataOperationCanceledException {
		final BranchingProcess<LETTER, PLACE> finPre = new FinitePrefix<>(mServices, mOperand).getResult();
		return reachableTransitions(finPre);
	}
	
	/**
	 * From a complete finite prefix compute the reachable transitions of the original Petri net.
	 * A transition t is reachable iff there is a reachable marking enabling t.
	 * @param finPre complete finite Prefix of a Petri net N
	 * @return reachable transitions in N
	 */
	public static <LETTER, PLACE> Set<ITransition<LETTER, PLACE>> reachableTransitions(
			BranchingProcess<LETTER, PLACE> finPre) {
		return finPre.getEvents().stream().map(Event::getTransition)
				// finPre contains dummy root-event which does not correspond to any transition
				.filter(Objects::nonNull)
				.collect(Collectors.toSet());
	}

	private Set<PLACE> requiredPlaces() {
		final Set<PLACE> requiredPlaces = new HashSet<>();
		for (final ITransition<LETTER, PLACE> trans : mReachableTransitions) {
			requiredPlaces.addAll(mOperand.getPredecessors(trans));
			// successor places are only required
			// if they are predecessors of another reachable transition
			// or if they are accepting
		}
		acceptingSuccPlaces().forEach(requiredPlaces::add);
		alwaysAcceptingPlaces().findAny().ifPresent(requiredPlaces::add);
		return requiredPlaces;
	}
	
	private Stream<PLACE> acceptingSuccPlaces() {
		return mOperand.getAcceptingPlaces().stream().filter(
				accPlace -> SetOperations.intersecting(mOperand.getPredecessors(accPlace), mReachableTransitions));
	}
	
	private Stream<PLACE> alwaysAcceptingPlaces() {
		return acceptingInitialPlaces().filter(
				accIniPlace -> SetOperations.disjoint(mOperand.getSuccessors(accIniPlace), mReachableTransitions));
	}
	
	private Stream<PLACE> acceptingInitialPlaces() {
		return mOperand.getAcceptingPlaces().stream().filter(mOperand.getInitialPlaces()::contains);
	}

	private void rebuildNetWithoutDeadNodes() {
		requiredPlaces().forEach(this::rebuildPlace);
		mReachableTransitions.forEach(this::rebuildTransition);
	}

	private void rebuildPlace(PLACE place) {
		final boolean isInitial = mOperand.getInitialPlaces().contains(place);
		final boolean isAccepting = mOperand.getAcceptingPlaces().contains(place);
		mResult.addPlace(place, isInitial, isAccepting);
	}

	private void rebuildTransition(ITransition<LETTER, PLACE> trans) {
		final Set<PLACE> succ = SetOperations.intersection(mOperand.getSuccessors(trans), mResult.getPlaces());
		mResult.addTransition(trans.getSymbol(), mOperand.getPredecessors(trans), succ);
	}

	@Override
	public BoundedPetriNet<LETTER, PLACE> getResult() {
		return mResult;
	}

	@Override
	protected IPetriNet<LETTER, PLACE> getOperand() {
		return mOperand;
	}
	
	@Override
	public boolean checkResult(final CRSF stateFactory) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Testing correctness of " + getOperationName());
		}
		final boolean correct = new IsEquivalent<>(mServices, stateFactory,
				netToNwa(stateFactory, mOperand), netToNwa(stateFactory, mResult)).getResult();
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of " + getOperationName());
		}
		return correct;
	}

	private INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> netToNwa(
			final CRSF stateFactory, final IPetriNet<LETTER, PLACE> net) {
		return new PetriNet2FiniteAutomaton<>(mServices, stateFactory, net).getResult();
	}
	
	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		final AutomataOperationStatistics statistics = new AutomataOperationStatistics();

		statistics.addKeyValuePair(
				StatisticsType.PETRI_REMOVED_PLACES , mOperand.getPlaces().size() - mResult.getPlaces().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_REMOVED_TRANSITIONS, mOperand.getTransitions().size() - mResult.getTransitions().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_REMOVED_FLOW, mOperand.flowSize() - mResult.flowSize());

		statistics.addKeyValuePair(
				StatisticsType.PETRI_ALPHABET, mResult.getAlphabet().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_PLACES , mResult.getPlaces().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_TRANSITIONS, mResult.getTransitions().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_FLOW, mResult.flowSize());

		return statistics;
	}

}



