package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;

public class RabinWordCheck<LETTER, PLACE> extends UnfoldingInfiniteWordCheck<LETTER, PLACE> {

	public RabinWordCheck(final AutomataLibraryServices services, final BranchingProcess<LETTER, PLACE> unfolding,
			final IRabinPetriNet<LETTER, PLACE> net) {
		super(services, unfolding, net);
	}

	// mAccptLoopEvents.contains(event) && !finitePlaceInLoop(event, mAccptLoopEventToLoopHeadMap.get(event))
	@Override
	boolean meetsConditionsToBeBaseOfLassoConfiguration(final Event<LETTER, PLACE> event) {
		return mAccptLoopEvents.contains(event) && !finitePlaceInLoop(event, mAccptLoopEventToLoopHeadMap.get(event));
	}

	@Override
	final boolean extendsConfiguration(final Event<LETTER, PLACE> event,
			final PotentialLassoConfiguration<LETTER, PLACE> config) {
		for (final Event<LETTER, PLACE> event2 : config.getEndEvents()) {
			if (!mUnfolding.eventsInConcurrency(event, event2)) {
				return false;
			}
		}
		return true;
	}

	private boolean finitePlaceInLoop(final Event<LETTER, PLACE> event, final Set<Event<LETTER, PLACE>> set) {
		List<Event<LETTER, PLACE>> sortedConfigArrayList = new ArrayList<>();
		sortedConfigArrayList = event.getLocalConfiguration().getSortedConfiguration(new EsparzaRoemerVoglerOrder<>());
		boolean inLoop = false;
		for (final Event<LETTER, PLACE> configEvent : sortedConfigArrayList) {
			if (set.contains(configEvent)) {
				inLoop = true;
			}
			if (inLoop) {
				if (configEvent.getSuccessorConditions().stream()
						.anyMatch(mUnfolding.getAcceptingConditions()::contains)) {
					return true;
				}
			}
		}
		return false;
	}
}
