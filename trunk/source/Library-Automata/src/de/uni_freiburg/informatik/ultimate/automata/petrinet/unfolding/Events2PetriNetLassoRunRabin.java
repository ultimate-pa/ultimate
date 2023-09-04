package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.Iterator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;

/**
 * A class that checks Rabin acceptance over a proposed Stem & Loop, returns a accepting Lasso word if the proposed
 * arguments are accepting
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            type of letters
 * @param <PLACE>
 *            type of places
 */
public class Events2PetriNetLassoRunRabin<LETTER, PLACE> extends Events2PetriNetLassoRunBuchi<LETTER, PLACE> {

	public Events2PetriNetLassoRunRabin(final List<Event<LETTER, PLACE>> configLoopPart,
			final List<Event<LETTER, PLACE>> configStemPart, final BranchingProcess<LETTER, PLACE> unfolding) {
		super(configLoopPart, configStemPart, unfolding);
	}

	/**
	 * overrides the Buchi acceptance condition with the Rabin acceptance condition
	 */
	@Override
	public boolean isAccepted() {
		final Iterator<PLACE> candidateIterator =
				mConfigLoopPart.stream().flatMap(x -> x.getTransition().getSuccessors().stream()).iterator();
		boolean result = false;
		// this checks that a accepting place exists and no finite place exists in the loop
		while (candidateIterator.hasNext()) {
			final PLACE candidate = candidateIterator.next();
			if (((IRabinPetriNet<LETTER, PLACE>) mUnfolding.getNet()).isFinite(candidate)) {
				return false;
			}
			result = result || mUnfolding.getNet().isAccepting(candidate);

		}
		return result;
	}
}
