package de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

/**
 * Wraps an {@code IPetriNet} (representing a Büchi-Petri-Net) into an {@code IRabinPetriNet}, simply with no finite
 * place.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class RabinPetriNetWrapper<LETTER, PLACE> implements IRabinPetriNet<LETTER, PLACE> {
	private final IPetriNet<LETTER, PLACE> mPetriNet;

	public RabinPetriNetWrapper(final IPetriNet<LETTER, PLACE> petriNet) {
		mPetriNet = petriNet;
	}

	@Override
	public Set<Transition<LETTER, PLACE>> getSuccessors(final PLACE place) {
		return mPetriNet.getSuccessors(place);
	}

	@Override
	public Set<Transition<LETTER, PLACE>> getPredecessors(final PLACE place) {
		return mPetriNet.getPredecessors(place);
	}

	@Override
	public Collection<ISuccessorTransitionProvider<LETTER, PLACE>>
			getSuccessorTransitionProviders(final Set<PLACE> mustPlaces, final Set<PLACE> mayPlaces) {
		return mPetriNet.getSuccessorTransitionProviders(mustPlaces, mayPlaces);
	}

	@Override
	public Set<PLACE> getInitialPlaces() {
		return mPetriNet.getInitialPlaces();
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mPetriNet.getAlphabet();
	}

	@Override
	public boolean hasModifiableAlphabet() {
		return mPetriNet.hasModifiableAlphabet();
	}

	@Override
	public Set<PLACE> getPlaces() {
		return mPetriNet.getPlaces();
	}

	@Override
	public Set<Transition<LETTER, PLACE>> getTransitions() {
		return mPetriNet.getTransitions();
	}

	@Override
	public Set<PLACE> getAcceptingPlaces() {
		return mPetriNet.getAcceptingPlaces();
	}

	@Override
	public IElement transformToUltimateModel(final AutomataLibraryServices services)
			throws AutomataOperationCanceledException {
		return mPetriNet.transformToUltimateModel(services);
	}

	@Override
	public boolean isAccepting(final Marking<PLACE> marking) {
		return mPetriNet.isAccepting(marking);
	}

	@Override
	public boolean isAccepting(final PLACE place) {
		return mPetriNet.isAccepting(place);
	}

	@Override
	public int flowSize() {
		return mPetriNet.flowSize();
	}

	@Override
	public int size() {
		return mPetriNet.size();
	}

	@Override
	public String sizeInformation() {
		return mPetriNet.sizeInformation();
	}

	@Override
	public String toString() {
		final StringBuilder result = new StringBuilder(mPetriNet.toString());
		result.insert(0, "Rabin");
		result.delete(result.lastIndexOf("}") + 1, result.length());
		result.append(",\n");
		result.append("	finitePlaces = {}\n);");
		return result.toString();
	}

	@Override
	public Set<PLACE> getFinitePlaces() {
		return Set.of();
	}

	@Override
	public boolean isFinite(final PLACE place) {
		return false;
	}
}
