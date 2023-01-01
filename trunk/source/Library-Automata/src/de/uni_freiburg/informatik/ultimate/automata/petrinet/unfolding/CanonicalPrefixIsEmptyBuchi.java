package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Checks if complete finite prefix contains accepting lasso configuration.
 *
 *
 */
public class CanonicalPrefixIsEmptyBuchi<LETTER, PLACE> {
	BranchingProcess<LETTER, PLACE> mCompletePrefix;
	Set<Event<LETTER, PLACE>> mCutoffEventsWithDistantCompanion = new HashSet<>();
	Set<Event<LETTER, PLACE>> mLoopCutoffEvents = new HashSet<>();
	Set<Event<LETTER, PLACE>> mOriginLoopCutoffEvents = new HashSet<>();
	private PetriNetLassoRun<LETTER, PLACE> mRun = null;
	AutomataLibraryServices mServices;
	protected final ILogger mLogger;
	Boolean searchAllLassoTypes = false;

	public CanonicalPrefixIsEmptyBuchi(final AutomataLibraryServices services,
			final BranchingProcess<LETTER, PLACE> completePrefix) throws PetriNetNot1SafeException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mCompletePrefix = completePrefix;
		mLogger.info("Starting emptiness check.");
		classifyCutoffEvents();
		investigateCutOffs();
		mLogger.info("Finished emptiness check, language is " + (getResult() ? "empty" : "not empty"));
	}

	public PetriNetLassoRun<LETTER, PLACE> getLassoRun() {
		return mRun;
	}

	private boolean getResult() {
		return mRun == null;
	}

	private void classifyCutoffEvents() {
		mLogger.info("Starting cutoff event analysis.");
		for (final Event<LETTER, PLACE> event : mCompletePrefix.getCutoffEvents()) {
			if (event.getLocalConfiguration().contains(event.getCompanion())) {
				mLoopCutoffEvents.add(event);
			} else if (event.getCompanion().getTransition() == null) {
				mOriginLoopCutoffEvents.add(event);
			} else {
				mCutoffEventsWithDistantCompanion.add(event);
			}
		}
		mLogger.info("Ended cutoff event analysis.");
	}

	private void investigateCutOffs() throws PetriNetNot1SafeException {
		investigateTypeOneLassos();

		// Type two lassos are already searched in PetrinetUnfolderBuchi.
		if (searchAllLassoTypes) {
			investigateTypeTwoLassos();
		}

		investigateTypeThreeLassos();
	}

	/**
	 * (edge case) Lasso word contained in local configuration where the stem-event of the Unfolding is an event
	 * companion.
	 *
	 * @throws PetriNetNot1SafeException
	 */
	private void investigateTypeThreeLassos() throws PetriNetNot1SafeException {
		mLogger.info("Type 3 Lasso search started.");
		final Set<Event<LETTER, PLACE>> acceptingEvents = new HashSet<>();
		for (final Condition<LETTER, PLACE> condition : mCompletePrefix.getAcceptingConditions()) {
			acceptingEvents.add(condition.getPredecessorEvent());
		}
		for (final Event<LETTER, PLACE> event : mCutoffEventsWithDistantCompanion) {
			for (final Event<LETTER, PLACE> event2 : acceptingEvents) {
				if (event.getLocalConfiguration().contains(event2)) {
					furtherUnfoldFrom(event, event.getCompanion());
				}
			}

		}
		mLogger.info("Type 3 Lasso search ended.");
	}

	private void furtherUnfoldFrom(final Event<LETTER, PLACE> cutoff, final Event<LETTER, PLACE> companion)
			throws PetriNetNot1SafeException {
		final Set<Event<LETTER, PLACE>> acceptingEvents = new HashSet<>();
		for (final Condition<LETTER, PLACE> condition : mCompletePrefix.getAcceptingConditions()) {
			acceptingEvents.add(condition.getPredecessorEvent());
		}
		Event<LETTER, PLACE> currCompanionEvent = companion;
		Event<LETTER, PLACE> currCutoffEvent = cutoff;
		final List<Event<LETTER, PLACE>> followingEvents = new ArrayList<>();
		boolean found = false;
		boolean foundReal = false;
		while (!found) {
			final int size = followingEvents.size();
			for (final Event<LETTER, PLACE> event : mCompletePrefix.getCutoffEvents()) {
				if (event.getLocalConfiguration().contains(currCompanionEvent)) {
					if (followingEvents.contains(event)) {
						found = true;
						break;
					}
					for (final Event<LETTER, PLACE> event2 : event.getLocalConfiguration()
							.getSortedConfiguration(mCompletePrefix.getOrder())) {
						if (event2.getLocalConfiguration().contains(currCompanionEvent)) {
							followingEvents.add(event2);
						}
					}
					currCompanionEvent = event.getCompanion();
					currCutoffEvent = event;
					if (currCutoffEvent == cutoff) {
						found = true;
						foundReal = true;
						break;
					}
					continue;
				}
			}
			if (followingEvents.size() == size) {
				break;
			}
		}
		if (foundReal && followingEvents.stream().anyMatch(acceptingEvents::contains)) {
			final List<Event<LETTER, PLACE>> configLoopEvents = new ArrayList<>(followingEvents);
			final List<Event<LETTER, PLACE>> configStemEvents =
					new ArrayList<>(cutoff.getLocalConfiguration().getSortedConfiguration(mCompletePrefix.getOrder()));
			if (checkIfLassoConfigurationAccepted(configLoopEvents, configStemEvents)) {
				return;
			}
		}
	}

	/**
	 * (edge case) Lasso word contained in local configuration where the stem-event of the Unfolding is an event
	 * companion.
	 *
	 * @throws PetriNetNot1SafeException
	 */
	private void investigateTypeOneLassos() throws PetriNetNot1SafeException {
		mLogger.info("Type 1 Lasso search started.");
		for (final Event<LETTER, PLACE> event : mOriginLoopCutoffEvents) {
			final List<Event<LETTER, PLACE>> configLoopEvents = new ArrayList<>();
			for (final Event<LETTER, PLACE> configEvent : event.getLocalConfiguration()
					.getSortedConfiguration(mCompletePrefix.getOrder())) {
				configLoopEvents.add(configEvent);
			}
			if (checkIfLassoConfigurationAccepted(configLoopEvents, new ArrayList<>())) {
				return;
			}
		}
		mLogger.info("Type 1 Lasso search ended.");
	}

	/**
	 * Lasso word contained in local configuration
	 *
	 * @throws PetriNetNot1SafeException
	 */
	private void investigateTypeTwoLassos() throws PetriNetNot1SafeException {
		mLogger.info("Type 2 Lasso search started.");
		for (final Event<LETTER, PLACE> event : mLoopCutoffEvents) {
			final List<Event<LETTER, PLACE>> configLoopEvents = new ArrayList<>();
			final List<Event<LETTER, PLACE>> configStemEvents = new ArrayList<>();
			for (final Event<LETTER, PLACE> configEvent : event.getLocalConfiguration()
					.getSortedConfiguration(mCompletePrefix.getOrder())) {
				if (configEvent != event.getCompanion()
						&& configEvent.getLocalConfiguration().contains(event.getCompanion())) {
					configLoopEvents.add(configEvent);
				} else {
					configStemEvents.add(configEvent);
				}
			}
			if (checkIfLassoConfigurationAccepted(configLoopEvents, configStemEvents)) {
				return;
			}
		}
		mLogger.info("Type 2 Lasso search ended.");
	}

	private final boolean checkIfLassoConfigurationAccepted(final List<Event<LETTER, PLACE>> configLoopPart,
			final List<Event<LETTER, PLACE>> configStemPart) throws PetriNetNot1SafeException {
		final var buildAndCheck =
				new Events2PetriNetLassoRunBuchi<>(mServices, configLoopPart, configStemPart, mCompletePrefix);
		mRun = buildAndCheck.getLassoRun();
		return (mRun != null);
	}
}
