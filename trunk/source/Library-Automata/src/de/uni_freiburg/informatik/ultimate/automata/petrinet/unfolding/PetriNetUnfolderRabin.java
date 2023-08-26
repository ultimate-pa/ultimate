package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder.EventOrderEnum;

public class PetriNetUnfolderRabin<LETTER, PLACE> extends PetriNetUnfolderBuchi<LETTER, PLACE> {

	public PetriNetUnfolderRabin(final AutomataLibraryServices services, final IRabinPetriNet<LETTER, PLACE> operand,
			final EventOrderEnum order, final boolean sameTransitionCutOff, final boolean stopIfAcceptingRunFound)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services, operand, order, sameTransitionCutOff, stopIfAcceptingRunFound);

	}

	@SuppressWarnings("unused")
	private final boolean checkIfLassoConfigurationAccepted(final List<Event<LETTER, PLACE>> configLoopPart,
			final List<Event<LETTER, PLACE>> configStemPart) {
		mEvents2PetriNetLassoRunBuchi = new Events2PetriNetLassoRunRabin<LETTER, PLACE>(configLoopPart, configStemPart,
				mUnfolding, (IRabinPetriNet<LETTER, PLACE>) mOperand);
		return mEvents2PetriNetLassoRunBuchi.isAccepted();
	}

}
