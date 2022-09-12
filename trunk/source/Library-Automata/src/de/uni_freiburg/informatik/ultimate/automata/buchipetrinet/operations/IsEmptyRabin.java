package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.EsparzaRoemerVoglerOrder;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;

public class IsEmptyRabin<LETTER, PLACE> extends IsEmptyInfinite<LETTER, PLACE> {

	public IsEmptyRabin(final AutomataLibraryServices services, final BranchingProcess<LETTER, PLACE> unfolding,
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
		if (!config.extendsConfiguration(event)) {
			return false;
		}

		if (finitePlaceInLoop(event, config.getLoopheadEvent())) {
			return false;
		}

		for (final Event<LETTER, PLACE> event2 : config.getEndEvents()) {
			if (!mUnfolding.eventsInConcurrency(event, event2)) {
				return false;
			}
		}
		return true;
	}

	private boolean finitePlaceInLoop(final Event<LETTER, PLACE> event, final Event<LETTER, PLACE> loopHead) {
		List<Event<LETTER, PLACE>> sortedConfigArrayList = new ArrayList<>();
		sortedConfigArrayList = event.getLocalConfiguration().getSortedConfiguration(new EsparzaRoemerVoglerOrder<>());
		boolean inLoop = false;
		for (final Event<LETTER, PLACE> configEvent : sortedConfigArrayList) {
			if (configEvent == loopHead) {
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
