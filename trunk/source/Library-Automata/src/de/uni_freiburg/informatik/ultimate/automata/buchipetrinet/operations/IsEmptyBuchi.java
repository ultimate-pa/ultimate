package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;

public class IsEmptyBuchi<LETTER, PLACE> extends IsEmptyInfinite<LETTER, PLACE> {

	public IsEmptyBuchi(final AutomataLibraryServices services,
			final BranchingProcess<LETTER, PLACE> unfolding, final IPetriNetTransitionProvider<LETTER, PLACE> net) {
		super(services, unfolding, net);
	}

	@Override
	boolean meetsConditionsToBeBaseOfLassoConfiguration(final Event<LETTER, PLACE> event) {
		return mAccptLoopEvents.contains(event);
	}

	@Override
	boolean extendsConfiguration(final Event<LETTER, PLACE> event,
			final PotentialLassoConfiguration<LETTER, PLACE> config) {
		if (!config.extendsConfiguration(event)) {
			return false;
		}

		for (final Event<LETTER, PLACE> event2 : config.getEndEvents()) {
			if (!mUnfolding.eventsInConcurrency(event, event2)) {
				return false;
			}
		}
		return true;
	}
}
