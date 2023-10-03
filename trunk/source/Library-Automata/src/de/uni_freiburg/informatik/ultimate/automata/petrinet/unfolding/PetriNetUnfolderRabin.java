package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder.EventOrderEnum;

/**
 * A unfolder that extends {@link PetriNetUnfolderBuchi} and uses a {@link IRabinPetriNet} to check for the Rabin
 * condition
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            type of letters
 * @param <PLACE>
 *            type of places
 */
public class PetriNetUnfolderRabin<LETTER, PLACE> extends PetriNetUnfolderBuchi<LETTER, PLACE> {

	// ensures that operand is of type {@link IRabinPetriNet}
	public PetriNetUnfolderRabin(final AutomataLibraryServices services, final IRabinPetriNet<LETTER, PLACE> operand,
			final EventOrderEnum order, final boolean sameTransitionCutOff, final boolean stopIfAcceptingRunFound)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services, operand, order, sameTransitionCutOff, stopIfAcceptingRunFound);

	}

	@Override
	protected boolean checkIfLassoConfigurationAccepted(final List<Event<LETTER, PLACE>> configLoopPart,
			final List<Event<LETTER, PLACE>> configStemPart) {
		mEvents2PetriNetLassoRunBuchi = new Events2PetriNetLassoRunRabin<>(configLoopPart, configStemPart, mUnfolding);
		mLogger.error(configStemPart.toString() + configLoopPart.toString());
		return mEvents2PetriNetLassoRunBuchi.isAccepted();
	}

}
