package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class PartialConfigurationBeingBuilt<LETTER, PLACE> {
	private final Event<LETTER, PLACE> mCurrentCompanionEvent;
	private final List<List<Event<LETTER, PLACE>>> mSortedPartialLocalConfigs;
	private final Set<Event<LETTER, PLACE>> mCutoffEvents;

	public PartialConfigurationBeingBuilt(final Event<LETTER, PLACE> currentCompanionEvent,
			final List<List<Event<LETTER, PLACE>>> sortedPartialConfigEventsList,
			final Set<Event<LETTER, PLACE>> cutoffEvents) {
		mCurrentCompanionEvent = currentCompanionEvent;
		mSortedPartialLocalConfigs = sortedPartialConfigEventsList;
		mCutoffEvents = cutoffEvents;
	}

	public Event<LETTER, PLACE> getCurrentCompanionEvent() {
		return mCurrentCompanionEvent;
	}

	public List<List<Event<LETTER, PLACE>>> getSortedPartialLocalConfigs() {
		return mSortedPartialLocalConfigs;
	}

	public Set<Event<LETTER, PLACE>> getCutoffEvents() {
		return mCutoffEvents;
	}

	public PartialConfigurationBeingBuilt<LETTER, PLACE> getExtendedCopy(final Event<LETTER, PLACE> event,
			final ConfigurationOrder<LETTER, PLACE> order) {
		final List<Event<LETTER, PLACE>> newlocalConfigEvents = new ArrayList<>();
		for (final Event<LETTER, PLACE> configEvent : event.getLocalConfiguration().getSortedConfiguration(order)) {
			if (configEvent.getLocalConfiguration().contains(getCurrentCompanionEvent())) {
				newlocalConfigEvents.add(event);
			}
		}
		final List<List<Event<LETTER, PLACE>>> newconfigSetList = new ArrayList<>(getSortedPartialLocalConfigs());
		newconfigSetList.add(newlocalConfigEvents);
		final Set<Event<LETTER, PLACE>> seenEvents = new HashSet<>(getCutoffEvents());
		seenEvents.add(event);
		return new PartialConfigurationBeingBuilt<>(event.getCompanion(), newconfigSetList, seenEvents);
	}
}
