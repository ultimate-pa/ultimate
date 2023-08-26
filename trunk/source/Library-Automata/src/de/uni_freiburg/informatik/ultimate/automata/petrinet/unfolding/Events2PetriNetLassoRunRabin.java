package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;

public class Events2PetriNetLassoRunRabin<LETTER, PLACE> extends Events2PetriNetLassoRunBuchi<LETTER, PLACE> {

	IRabinPetriNet<LETTER, PLACE> mRabrinPetriNet;

	public Events2PetriNetLassoRunRabin(final List<Event<LETTER, PLACE>> configLoopPart,
			final List<Event<LETTER, PLACE>> configStemPart, final BranchingProcess<LETTER, PLACE> unfolding,
			final IRabinPetriNet<LETTER, PLACE> rabinPetriNet) {
		super(configLoopPart, configStemPart, unfolding);
		mRabrinPetriNet = rabinPetriNet;
	}

	@Override
	public boolean isAccepted() {
		return mConfigLoopPart.stream().flatMap(x -> x.getTransition().getSuccessors().stream())
				.filter(y -> !mRabrinPetriNet.isFinite(y)).anyMatch(mUnfolding.getNet()::isAccepting);
	}
}
