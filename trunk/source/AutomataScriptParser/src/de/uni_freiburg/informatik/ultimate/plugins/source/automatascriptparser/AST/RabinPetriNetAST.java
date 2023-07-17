package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * A adaptation of acceptor Petri net with finite states; Intended for use with Rabin automata
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 */
public class RabinPetriNetAST extends AutomatonAST {

	private List<String> mAlphabet;
	private List<String> mPlaces;

	private List<PetriNetTransitionAST> mTransitions;
	private PetriNetMarkingListAST mInitialMarkings;
	private List<String> mAcceptingPlaces;

	private List<String> mFinitePlaces;

	public RabinPetriNetAST(final ILocation loc, final String name) {
		super(loc, name);
	}

	public List<String> getAlphabet() {
		return mAlphabet;
	}

	public void setAlphabet(final List<String> alphabet) {
		mAlphabet = alphabet;
	}

	public List<String> getPlaces() {
		return mPlaces;
	}

	public void setPlaces(final List<String> places) {
		mPlaces = places;
	}

	public List<PetriNetTransitionAST> getTransitions() {
		return mTransitions;
	}

	public void setTransitions(final List<PetriNetTransitionAST> transitions) {
		mTransitions = transitions;
	}

	public PetriNetMarkingListAST getInitialMarkings() {
		return mInitialMarkings;
	}

	public void setInitialMarkings(final PetriNetMarkingListAST initialMarkings) {
		mInitialMarkings = initialMarkings;
	}

	public List<String> getAcceptingPlaces() {
		return mAcceptingPlaces;
	}

	public void setAcceptingPlaces(final List<String> acceptingPlaces) {
		mAcceptingPlaces = acceptingPlaces;
	}

	public List<String> getFinitePlaces() {
		return mFinitePlaces;
	}

	public void setFinitePlaces(final List<String> finitePlaces) {
		mFinitePlaces = finitePlaces;
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("RabinPetriNet(" + mName + "): " + "[#alphabet: ");
		builder.append(getAlphabet().size());
		builder.append(" #places: ");
		builder.append(getPlaces().size());
		builder.append(" #acceptingPlaces: ");
		builder.append(getAcceptingPlaces().size());
		builder.append(" #finitePlaces: ");
		builder.append(getFinitePlaces().size());
		builder.append(" #transitions: ");
		builder.append(getTransitions().size());
		builder.append("]");
		return builder.toString();
	}
}
