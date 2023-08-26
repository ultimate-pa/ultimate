package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.Iterator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;

public class Events2PetriNetLassoRunRabin<LETTER, PLACE> extends Events2PetriNetLassoRunBuchi<LETTER, PLACE> {

	IRabinPetriNet<LETTER, PLACE> mRabinPetriNet;

	public Events2PetriNetLassoRunRabin(final List<Event<LETTER, PLACE>> configLoopPart,
			final List<Event<LETTER, PLACE>> configStemPart, final BranchingProcess<LETTER, PLACE> unfolding,
			final IRabinPetriNet<LETTER, PLACE> rabinPetriNet) {
		super(configLoopPart, configStemPart, unfolding);
		mRabinPetriNet = rabinPetriNet;
	}

	@Override
	public boolean isAccepted() {
		final Iterator<PLACE> candidateIterator =
				mConfigLoopPart.stream().flatMap(x -> x.getTransition().getSuccessors().stream()).iterator();
		boolean result = false;
		while (candidateIterator.hasNext()) {
			final PLACE candidate = candidateIterator.next();
			if (mRabinPetriNet.isFinite(candidate)) {
				return false;
			}
			if (mUnfolding.getNet().isAccepting(candidate)) {
				result = true;
			}
		}
		return result;
	}
}
