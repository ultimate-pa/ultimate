package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Set of events which local configurations in the unfolding build a configurations which might be a lasso
 * Configuration, i.e. a configuration which contains words accepted by the infinite petri net which the unfolding is
 * done on.
 *
 * @param <LETTER>
 * @param <PLACE>
 */
public class FireSequenceInProgress<LETTER, PLACE> {
	private final List<Transition<LETTER, PLACE>> stillToFireTransitions;
	private final List<Transition<LETTER, PLACE>> mOrderedLoopTransitionList;
	private final List<Marking<PLACE>> mOrderedLoopMarkingList;
	private final List<LETTER> mOrderedLoopLetters;
	private final Set<Transition<LETTER, PLACE>> mStartConfigSet;
	private Marking<PLACE> mCurrentMarking;
	private final Set<Event<LETTER, PLACE>> mStartEvents;

	// Set<Pair<Set<Transition<LETTER, PLACE>>, Pair<Marking<PLACE>, List<LETTER>>>>

	// public FireSequenceInProgress(final Set<Transition<LETTER, PLACE>> startConfig,
	// final List<Transition<LETTER, PLACE>> SCC, final Marking<PLACE> initM,
	// final List<Event<LETTER, PLACE>> eventList, final Set<Event<LETTER, PLACE>> startEvents) {
	// mStartConfigSet = new HashSet<>(startConfig);
	// stillToFireTransitions = new ArrayList<>(SCC);
	// mCurrentMarking = new Marking<>(ImmutableSet.of(initM.stream().collect(Collectors.toSet())));
	// mEventList = new ArrayList<>(eventList);
	// mStartEvents = new HashSet<>(startEvents);
	// mOrderedLoopTransitionList = new ArrayList<>();
	// mOrderedLoopMarkingList = new ArrayList<>();
	// mOrderedLoopLetters = new ArrayList<>();
	// }

	/**
	 *
	 * @param alreadyShotTransitions
	 * @param currentMarking
	 * @param stemLetters
	 * @param startConfig
	 * @param SCC
	 * @param initM
	 * @param startEvents
	 * @param eventlist
	 */
	public FireSequenceInProgress(final List<Transition<LETTER, PLACE>> alreadyShotTransitions,
			final List<Marking<PLACE>> markingList, final List<LETTER> stemLetters,
			final Set<Transition<LETTER, PLACE>> startConfig, final List<Transition<LETTER, PLACE>> SCC,
			final Marking<PLACE> initM, final Set<Event<LETTER, PLACE>> startEvents) {
		mOrderedLoopTransitionList = new ArrayList<>(alreadyShotTransitions);
		mOrderedLoopMarkingList = new ArrayList<>();
		for (final Marking<PLACE> marking : markingList) {
			mOrderedLoopMarkingList.add(new Marking<>(ImmutableSet.of(marking.stream().collect(Collectors.toSet()))));
		}
		mOrderedLoopLetters = new ArrayList<>(stemLetters);
		mStartConfigSet = new HashSet<>(startConfig);
		stillToFireTransitions = new ArrayList<>(SCC);
		mCurrentMarking = new Marking<>(ImmutableSet.of(initM.stream().collect(Collectors.toSet())));
		mStartEvents = new HashSet<>(startEvents);
	}

	public void addNewIteration(final Transition<LETTER, PLACE> transition, final LETTER letter)
			throws PetriNetNot1SafeException {
		stillToFireTransitions.remove(transition);
		mOrderedLoopTransitionList.add(transition);
		mCurrentMarking = mCurrentMarking.fireTransition(transition);
		mOrderedLoopMarkingList.add(mCurrentMarking);
		mOrderedLoopLetters.add(letter);

	}

	public Marking<PLACE> getCurrentMarking() {
		return mCurrentMarking;
	}

	public Set<Transition<LETTER, PLACE>> getStartConfigSet() {
		return mStartConfigSet;
	}

	public List<Marking<PLACE>> getOrderedLoopMarkingList() {
		return mOrderedLoopMarkingList;
	}

	public List<LETTER> getOrderedLoopLetters() {
		return mOrderedLoopLetters;
	}

	public List<Transition<LETTER, PLACE>> getOrderedLoopTransitionList() {
		return mOrderedLoopTransitionList;
	}

	public List<Transition<LETTER, PLACE>> getstillToFireTransitions() {
		return stillToFireTransitions;
	}

	public FireSequenceInProgress<LETTER, PLACE> getCopy() {

		final List<Transition<LETTER, PLACE>> newstillToFireTransitions = new ArrayList<>(stillToFireTransitions);
		final List<Transition<LETTER, PLACE>> newOrderedLoopTransitionList =
				new ArrayList<>(mOrderedLoopTransitionList);
		final List<Marking<PLACE>> newOrderedLoopMarkingList = new ArrayList<>(mOrderedLoopMarkingList);
		final List<LETTER> newOrderedLoopLetters = new ArrayList<>(mOrderedLoopLetters);
		final Set<Transition<LETTER, PLACE>> newStartConfigSet = new HashSet<>(mStartConfigSet);
		final Marking<PLACE> newCurrentMarking =
				new Marking<>(ImmutableSet.of(mCurrentMarking.stream().collect(Collectors.toSet())));
		final Set<Event<LETTER, PLACE>> newStartEvents = new HashSet<>(mStartEvents);
		final var newConfig = new FireSequenceInProgress<>(newOrderedLoopTransitionList, newOrderedLoopMarkingList,
				newOrderedLoopLetters, newStartConfigSet, newstillToFireTransitions, newCurrentMarking, newStartEvents);

		return newConfig;
	}

	public void completeMarkingList() {
		final var first = mOrderedLoopMarkingList.get(0);
		mOrderedLoopMarkingList.add(first);
	}

	public void removeDoubleLoopHead() {
		mOrderedLoopTransitionList.remove(0);
		mOrderedLoopLetters.remove(0);
	}

	public Set<Event<LETTER, PLACE>> getmStartEvents() {
		return mStartEvents;
	}

}
