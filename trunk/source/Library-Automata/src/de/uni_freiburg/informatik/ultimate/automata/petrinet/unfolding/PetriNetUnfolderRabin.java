package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder.EventOrderEnum;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * A unfolder that extends {@link PetriNetUnfolderBuchi} and uses a {@link IRabinPetriNet} to check for the Rabin
 * condition
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            type of letters
 * @param <PLACE>
 *            type of places
 */
public class PetriNetUnfolderRabin<LETTER, PLACE> extends PetriNetUnfolderBuchi<LETTER, PLACE> {

	// ensures that operand is of type {@link IRabinPetriNet}
	public PetriNetUnfolderRabin(final AutomataLibraryServices services, final IRabinPetriNet<LETTER, PLACE> operand,
			final EventOrderEnum order, final boolean sameTransitionCutOff, final boolean stopIfAcceptingRunFound)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services, operand, order, sameTransitionCutOff, stopIfAcceptingRunFound);

	}

	/**
	 * If we cannot assert that a run is nonfinite we have to use the new {@link Events2PetriNetLassoRunRabin} for
	 * proper acceptance
	 */
	@Override
	protected boolean checkIfLassoConfigurationAccepted(final List<Event<LETTER, PLACE>> configLoopPart,
			final List<Event<LETTER, PLACE>> configStemPart) {
		mEvents2PetriNetLassoRunBuchi = new Events2PetriNetLassoRunRabin<>(configLoopPart, configStemPart, mUnfolding);
		mLogger.error(configStemPart.toString() + configLoopPart.toString());
		return mEvents2PetriNetLassoRunBuchi.isAccepted();
	}

	/*
	 * for simplicity we say a event is Finite if its transition would fire in a Finite place
	 */
	private boolean isFinite(final Event<LETTER, PLACE> e) {
		return e.getTransition().getSuccessors().stream()
				.anyMatch(((IRabinPetriNet<LETTER, PLACE>) mOperand)::isFinite);
	}

	@Override
	protected boolean addAndCheck(final Event<LETTER, PLACE> event) throws PetriNetNot1SafeException {
		mUnfolding.addEvent(event);

		if (!event.isCutoffEvent() || isFinite(event)) {
			return false;
		}

		if (checkLocalConfigurationForLoop(event)) {
			return true;
		}

		/**
		 * Searches for lasso-words which are NOT fully contained in a local configuration and instead in a "partial
		 * configuration". An example of such a word would be c(fehg)^w contained in the Buchi-Petri-Net in
		 * "PartialConfigurationThesis.ats". Such words cannot be found in a local configuration (depending on the
		 * Unfolding algorithm of course).
		 *
		 * The rough algorithm to find such words in the Unfolding below is that we "backtrack" starting from a
		 * cutoff-event and if we encounter companion events during backtracking we jump to their respective
		 * cutoff-event(s). If, through this backtracking, we encounter the starting cutoff event again, we have found a
		 * partial configuration that builds a lasso-word.
		 */

		// per reachable cutoffEvent its path in the unfolding will be looked at once
		final HashSet<Event<LETTER, PLACE>> seenEvents = new HashSet<>(Set.of(event));
		// In this map our reversed Tree is saved indirectly by referencing the parents in our DFS
		final HashMap<Event<LETTER, PLACE>, Event<LETTER, PLACE>> treeMap = new HashMap<>();
		// Using a stack for the backtrack search which behaves like a tree-search (one companion event might have
		// multiple respective cutoff events, creating multiple branches of search).
		final ArrayDeque<Pair<Event<LETTER, PLACE>, Event<LETTER, PLACE>>> cutoffStack = new ArrayDeque<>();
		cutoffStack.push(new Pair<>(event, null));
		while (!cutoffStack.isEmpty()) {
			treeMap.put(cutoffStack.peekLast().getFirst(), cutoffStack.peekLast().getSecond());
			Event<LETTER, PLACE> previousEvent = cutoffStack.removeLast().getFirst();

			final List<Event<LETTER, PLACE>> reversesortedList =
					previousEvent.getLocalConfiguration().getSortedConfiguration(mUnfolding.getOrder());
			Collections.reverse(reversesortedList);
			// this is the cutoffEvent itself
			reversesortedList.remove(0);
			for (final Event<LETTER, PLACE> configurationEvent : reversesortedList) {
				// we oppress finite traces, this ensures every time we see a cutoffEvent it is reached in a nonfinite
				// context and closed loops will also be nonfinite
				if (isFinite(configurationEvent)) {
					break;
				}
				treeMap.put(configurationEvent, previousEvent);
				if (configurationEvent.isCompanion()) {

					for (final Event<LETTER, PLACE> cutoffEvent : configurationEvent
							.getCutoffEventsThisIsCompanionTo()) {
						if (event.equals(cutoffEvent)) {
							final List<Event<LETTER, PLACE>> configLoopEvents = new ArrayList<>();
							Event<LETTER, PLACE> loopEvent = configurationEvent;
							// if we know that previousEvent can be enabled by event, we can trace our tree back to
							// event and get a nonfinite loop
							while (!loopEvent.equals(event)) {
								loopEvent = treeMap.get(loopEvent);
								configLoopEvents.add(loopEvent);
							}
							final List<Event<LETTER, PLACE>> configStemEvents =
									event.getLocalConfiguration().getSortedConfiguration(mUnfolding.getOrder());
							if (super.checkIfLassoConfigurationAccepted(configLoopEvents, configStemEvents)) {
								return true;
							}
						}
						if (seenEvents.add(cutoffEvent) && !isFinite(cutoffEvent)) {
							cutoffStack.offer(new Pair<>(cutoffEvent, previousEvent));
						}
					}
				}
				previousEvent = configurationEvent;
			}
		}
		return false;
	}
}
