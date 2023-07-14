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

	/**
	 *
	 */
	// private static final long serialVersionUID = -6021451678169305249L;
	private List<String> malphabet;
	private List<String> mplaces;

	private List<PetriNetTransitionAST> mtransitions;
	private PetriNetMarkingListAST minitialMarkings;
	private List<String> macceptingPlaces;

	private List<String> mFinitePlaces;

	public RabinPetriNetAST(final ILocation loc, final String name) {
		super(loc, name);
	}

	public List<String> getAlphabet() {
		return malphabet;
	}

	public void setAlphabet(final List<String> malphabet) {
		this.malphabet = malphabet;
	}

	public List<String> getPlaces() {
		return mplaces;
	}

	public void setPlaces(final List<String> mplaces) {
		this.mplaces = mplaces;
	}

	public List<PetriNetTransitionAST> getTransitions() {
		return mtransitions;
	}

	public void setTransitions(final List<PetriNetTransitionAST> mtransitions) {
		this.mtransitions = mtransitions;
	}

	public PetriNetMarkingListAST getInitialMarkings() {
		return minitialMarkings;
	}

	public void setInitialMarkings(final PetriNetMarkingListAST minitialMarkings) {
		this.minitialMarkings = minitialMarkings;
	}

	public List<String> getAcceptingPlaces() {
		return macceptingPlaces;
	}

	public void setAcceptingPlaces(final List<String> macceptingPlaces) {
		this.macceptingPlaces = macceptingPlaces;
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
