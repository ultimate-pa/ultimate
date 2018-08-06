package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.HashSet;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.function.Predicate;
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
		final BranchingProcess<LETTER, PLACE> finPre = new FinitePrefix<>(mServices, mOperand).getResult();
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

}



