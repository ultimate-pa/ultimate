package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder.EventOrderEnum;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Subclass of {@PetriNetUnfolder} which implements the lasso-word search of a Buchi-Petri-Net during its Unfolding.
 * Algorithm(s) based on "Omega-Petri-Nets for termination analysis" thesis.
 *
 * @param <LETTER>
 * @param <PLACE>
 */
public class PetriNetUnfolderBuchi<LETTER, PLACE>
		extends PetriNetUnfolderBase<LETTER, PLACE, PetriNetLassoRun<LETTER, PLACE>> {
	public PetriNetUnfolderBuchi(final AutomataLibraryServices services,
			final IPetriNetSuccessorProvider<LETTER, PLACE> operand, final EventOrderEnum order,
			final boolean sameTransitionCutOff, final boolean stopIfAcceptingRunFound)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services, operand, order, sameTransitionCutOff, stopIfAcceptingRunFound);
	}

	@Override
	protected boolean checkInitialPlacesAndCreateRun() {
		return false;
	}

	@Override
	protected boolean addAndCheck(final Event<LETTER, PLACE> event) throws PetriNetNot1SafeException {

		mUnfolding.addEvent(event);

		/**
		 * Special case of a lassoword appearing in a local configuration where its cutoff event has the
		 * Unfolding-stem-event as companion event, and thus needs special handling.
		 */
		if (event.isCutoffEvent() && event.getCompanion().getTransition() == null) {
			final List<Event<LETTER, PLACE>> configLoopEvents = new ArrayList<>();
			configLoopEvents.addAll(event.getLocalConfiguration().getSortedConfiguration(mUnfolding.getOrder()));
			if (checkIfLassoConfigurationAccepted(configLoopEvents, new ArrayList<>())) {
				return true;
			}
		}

		/**
		 * Searches for lasso-words which are fully contained in a local configuration of the Unfolding.
		 */
		if (event.isCutoffEvent() && event.getLocalConfiguration().contains(event.getCompanion())) {

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
			/**
			 * Searches for lasso-words which are NOT fully contained in a local configuration and instead in a "partial
			 * configuration". An example of such a word would be c(fehg)^w contained in the Buchi-Petri-Net in
			 * "PartialConfigurationThesis.ats". Such words cannot be found in a local configuration (depending on the
			 * Unfolding algorithm of course).
			 *
			 * The rough algorithm to find such words in the Unfolding below is that we "backtrack" starting from a
			 * cutoff-event and if we encounter companion events during backtracking we jump to their respective
			 * cutoff-event(s). If, through this backtracking, we encounter the starting cutoff event again, we have
			 * found a partial configuration that builds a lasso-word.
			 */
		} else if (event.isCutoffEvent()) {
			final Set<Event<LETTER, PLACE>> acceptingEvents = new HashSet<>();
			for (final Condition<LETTER, PLACE> condition : mUnfolding.getAcceptingConditions()) {
				acceptingEvents.add(condition.getPredecessorEvent());
			}

			// Using a stack for the backtrack search which behaves like a tree-search (one companion event might have
			// multiple respective cutoff events, creating multiple branches of search).
			final ArrayDeque<Pair<List<List<Event<LETTER, PLACE>>>, Event<LETTER, PLACE>>> worddBeingBuilt =
					new ArrayDeque<>();
			worddBeingBuilt
					.add(new Pair<List<List<Event<LETTER, PLACE>>>, Event<LETTER, PLACE>>(new ArrayList<>(), event));
			final Set<Event<LETTER, PLACE>> seenEvents = new HashSet<>();
			while (!worddBeingBuilt.isEmpty()) {
				final Pair<List<List<Event<LETTER, PLACE>>>, Event<LETTER, PLACE>> nextPair = worddBeingBuilt.pop();
				final List<Event<LETTER, PLACE>> reversesortedList =
						nextPair.getSecond().getLocalConfiguration().getSortedConfiguration(mUnfolding.getOrder());
				Collections.reverse(reversesortedList);
				final List<Event<LETTER, PLACE>> newList = new ArrayList<>();
				for (final Event<LETTER, PLACE> event2 : reversesortedList) {
					if (event2.isCompanion()) {
						nextPair.getFirst().add(newList);
						if (event2.getCutoffEventsThisIsCompanionTo().contains(event)) {
							final List<Event<LETTER, PLACE>> configLoopEvents = new ArrayList<>();
							final List<Event<LETTER, PLACE>> configStemEvents = new ArrayList<>();

							Collections.reverse(nextPair.getFirst());
							for (final List<Event<LETTER, PLACE>> localconfigList : nextPair.getFirst()) {
								configLoopEvents.addAll(localconfigList);
							}
							for (final Event<LETTER, PLACE> event3 : event.getLocalConfiguration()
									.getSortedConfiguration(mUnfolding.getOrder())) {
								configStemEvents.add(event3);
							}
							if (checkIfLassoConfigurationAccepted(configLoopEvents, configStemEvents)) {
								return true;
							}
						}
						// New backtrack-tree-path found through another companion event. We don't add event2 to the
						// list of events because it is not part of the word.
						for (final Event<LETTER, PLACE> cutoffEvent : event2.getCutoffEventsThisIsCompanionTo()) {
							if (seenEvents.contains(cutoffEvent)) {
								// to avoid looping
								continue;
							}
							seenEvents.add(cutoffEvent);
							worddBeingBuilt.add(new Pair<List<List<Event<LETTER, PLACE>>>, Event<LETTER, PLACE>>(
									new ArrayList<>(nextPair.getFirst()), cutoffEvent));
						}
						break;

					}
					// adding events we pass through, because they will build the lasso-word.
					newList.add(0, event2);
				}
			}
		}
		return false;
	}

	private final boolean checkIfLassoConfigurationAccepted(final List<Event<LETTER, PLACE>> configLoopPart,
			final List<Event<LETTER, PLACE>> configStemPart) throws PetriNetNot1SafeException {
		final var buildAndCheck =
				new Events2PetriNetLassoRunBuchi<>(mServices, configLoopPart, configStemPart, mUnfolding);
		mRun = buildAndCheck.getLassoRun();
		return mRun != null;
	}

	@Override
	protected void updateRunIfWanted(final Event<LETTER, PLACE> event) throws PetriNetNot1SafeException {
		// Nothing to do, the run was already created in checkIfLassoConfigurationAccepted
	}

	@Override
	boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<PLACE> stateFactory)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		// Not implemented yet
		return true;
	}
}
