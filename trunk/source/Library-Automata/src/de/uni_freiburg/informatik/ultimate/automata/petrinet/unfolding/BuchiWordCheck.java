package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.BuchiAccepts;

public class BuchiWordCheck<LETTER, PLACE> extends UnfoldingInfiniteWordCheck<LETTER, PLACE> {

	public BuchiWordCheck(final AutomataLibraryServices services, final BranchingProcess<LETTER, PLACE> unfolding,
			final IPetriNetTransitionProvider<LETTER, PLACE> net) {
		super(services, unfolding, net);
	}

	@Override
	boolean meetsConditionsToBeBaseOfLassoConfiguration(final Event<LETTER, PLACE> event) {
		return mAccptLoopEvents.contains(event);
	}

	@Override
	boolean extendsConfiguration(final Event<LETTER, PLACE> event,
			final PotentialLassoConfiguration<LETTER, PLACE> config) {
		for (final Event<LETTER, PLACE> event2 : config.getLoopEvents()) {
			if (!mUnfolding.eventsInConcurrency(event, event2)) {
				return false;
			}
		}
		return true;
	}

	@Override
	boolean isAccepted(final NestedLassoWord<LETTER> nestedLassoWord) throws PetriNetNot1SafeException {
		final BuchiAccepts<LETTER, PLACE> accepts = new BuchiAccepts<>(mServices, mOperand, nestedLassoWord);
		return accepts.getResult();
	}
}
