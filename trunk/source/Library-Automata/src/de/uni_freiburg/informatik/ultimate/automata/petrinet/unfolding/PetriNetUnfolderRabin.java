package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

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
		/**
		 * Special case of a lassoword appearing in a local configuration where its cutoff event has the
		 * Unfolding-stem-event as companion event, and thus needs special handling.
		 */
		if (event.getCompanion().getTransition() == null) {
			final List<Event<LETTER, PLACE>> configLoopEvents = new ArrayList<>();
			configLoopEvents.addAll(event.getLocalConfiguration().getSortedConfiguration(mUnfolding.getOrder()));
			if (checkIfLassoConfigurationAccepted(configLoopEvents, new ArrayList<>())) {
				return true;
			}
		}

		/**
		 * Searches for lasso-words which are fully contained in a local configuration of the Unfolding.
		 */
		if (event.getLocalConfiguration().contains(event.getCompanion())) {
			final List<Event<LETTER, PLACE>> configLoopEvents = new ArrayList<>();
			final List<Event<LETTER, PLACE>> configStemEvents = new ArrayList<>();
			for (final Event<LETTER, PLACE> configEvent : event.getLocalConfiguration()
					.getSortedConfiguration(mUnfolding.getOrder())) {
				if (configEvent != event.getCompanion()
						&& configEvent.getLocalConfiguration().contains(event.getCompanion())) {
					configLoopEvents.add(configEvent);
				} else {
					configStemEvents.add(configEvent);
				}
			}

			if (checkIfLassoConfigurationAccepted(configLoopEvents, configStemEvents)) {
				return true;
			}

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
		// Using a stack for the backtrack search which behaves like a tree-search (one companion event might have
		// multiple respective cutoff events, creating multiple branches of search).

		// In this map our reversed Tree is saved indirectly
		final HashSet<Event<LETTER, PLACE>> seenEvents = new HashSet<>(Set.of(event));
		final ArrayDeque<Pair<Event<LETTER, PLACE>, List<Event<LETTER, PLACE>>>> cutoffStack = new ArrayDeque<>();
		cutoffStack.push(new Pair<>(event, new ArrayList<>()));
		while (!cutoffStack.isEmpty()) {
			final List<Event<LETTER, PLACE>> currentWord =
					cutoffStack.peekLast().getSecond().stream().collect(Collectors.toList());
			final List<Event<LETTER, PLACE>> reversesortedList = cutoffStack.removeLast().getFirst()
					.getLocalConfiguration().getSortedConfiguration(mUnfolding.getOrder());

			Collections.reverse(reversesortedList);

			for (final Event<LETTER, PLACE> configurationEvent : reversesortedList) {
				if (isFinite(configurationEvent)) {
					break;
				}

				currentWord.add(configurationEvent);
				if (!configurationEvent.isCompanion()) {

					continue;
				}
				for (final Event<LETTER, PLACE> cutoffEvent : configurationEvent.getCutoffEventsThisIsCompanionTo()) {
					if (event.equals(cutoffEvent)) {
						final List<Event<LETTER, PLACE>> configLoopEvents =
								currentWord.stream().collect(Collectors.toList());
						Collections.reverse(configLoopEvents);
						configLoopEvents.remove(0);
						final List<Event<LETTER, PLACE>> configStemEvents =
								event.getLocalConfiguration().getSortedConfiguration(mUnfolding.getOrder());

						if (checkIfLassoConfigurationAccepted(configLoopEvents, configStemEvents)) {
							return true;
						}
					}

					if (seenEvents.add(cutoffEvent) && !isFinite(cutoffEvent)) {
						final List<Event<LETTER, PLACE>> copyWord = currentWord.stream().collect(Collectors.toList());
						copyWord.remove(copyWord.size() - 1);
						cutoffStack.offer(new Pair<>(cutoffEvent, Collections.unmodifiableList(copyWord)));
					}
				}

			}
		}
		return false;
	}
}
