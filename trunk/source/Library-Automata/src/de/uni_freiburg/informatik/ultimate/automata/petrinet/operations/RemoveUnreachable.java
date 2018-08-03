package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.HashSet;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.FinitePrefix;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Removes parts of a Petri Net that do not change its behavior.
 * <p>
 * A transition is unreachable iff it can never fire
 * (because there is no reachable marking covering all of its preceding places).
 * <p>
 * A place is unreachable iff it is not covered by any reachable marking.
 * <p>
 * This operation may also remove some of the reachable places if they are not needed, for insance
 * <ul>
 *   <li> all non-accepting places without a reachable successor transition
 *   <li> all but one accepting place without a reachable successor transition
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
public class RemoveUnreachable<LETTER, PLACE, CRSF extends IStateFactory<PLACE>>
		extends UnaryNetOperation<LETTER, PLACE, CRSF> {

	private final BoundedPetriNet<LETTER, PLACE> mOperand;
	
	/** {@link #mOperand} with only reachable transitions and required places. */
	private final BoundedPetriNet<LETTER, PLACE> mResult;
	
	private final Set<ITransition<LETTER, PLACE>> mReachableTransitions;
	
	public RemoveUnreachable(AutomataLibraryServices services, BoundedPetriNet<LETTER, PLACE> operand)
			throws AutomataOperationCanceledException {
		this(services, operand, null);
	}
	
	public RemoveUnreachable(AutomataLibraryServices services, BoundedPetriNet<LETTER, PLACE> operand,
			Set<ITransition<LETTER, PLACE>> reachableTransitions) throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		mResult = new BoundedPetriNet<>(services, operand.getAlphabet(), operand.constantTokenAmount());
		mReachableTransitions = reachableTransitions == null ? computeReachableTransitions() : reachableTransitions;
		rebuildNetWithoutDeadNodes();
	}

	private Set<ITransition<LETTER, PLACE>> computeReachableTransitions() throws AutomataOperationCanceledException {
		BranchingProcess<LETTER, PLACE> finPre = new FinitePrefix<>(mServices, mOperand).getResult();
		return finPre.getEvents().stream().map(Event::getTransition)
				// finPre contains dummy root-event which does not correspond to any transition
				.filter(Objects::nonNull)
				.collect(Collectors.toSet());
	}
	
	private Set<PLACE> requiredPlaces() {
		Set<PLACE> reachablePlaces = new HashSet<>();
		for (ITransition<LETTER, PLACE> trans : mReachableTransitions) {
			reachablePlaces.addAll(mOperand.getPredecessors(trans));
			reachablePlaces.addAll(mOperand.getSuccessors(trans));
		}

		Stream<PLACE> acceptingInitialPlaces = mOperand.getInitialPlaces().stream()
				.filter(mOperand.getAcceptingPlaces()::contains);
		// This is an optimization to remove more places.
		// The naive way would be to require all accepting initial places.
		Optional<PLACE> alwaysAcceptingPlace = acceptingInitialPlaces
				.filter(place -> !reachablePlaces.contains(place)).findAny();
		alwaysAcceptingPlace.ifPresent(reachablePlaces::add);

		return reachablePlaces;
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
		mResult.addTransition(trans.getSymbol(), mOperand.getPredecessors(trans), mOperand.getSuccessors(trans));
	}

	@Override
	public BoundedPetriNet<LETTER, PLACE> getResult() {
		return mResult;
	}

	@Override
	protected IPetriNet<LETTER, PLACE> getOperand() {
		return mOperand;
	}

}



