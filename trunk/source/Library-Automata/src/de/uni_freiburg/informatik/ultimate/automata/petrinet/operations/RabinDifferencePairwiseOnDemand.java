package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;

public class RabinDifferencePairwiseOnDemand<LETTER, PLACE, CRSF extends IPetriNet2FiniteAutomatonStateFactory<PLACE> & INwaInclusionStateFactory<PLACE>>
		extends DifferencePairwiseOnDemand<LETTER, PLACE, CRSF> {

	private final IRabinPetriNet<LETTER, PLACE> mWrappedResult;

	public RabinDifferencePairwiseOnDemand(final AutomataLibraryServices services,
			final IRabinPetriNet<LETTER, PLACE> minuendNet,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> subtrahendDfa)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services, minuendNet, subtrahendDfa);
		mWrappedResult = new RabinWrapper<>(super.getResult(), minuendNet);
	}

	@Override
	public IPetriNet<LETTER, PLACE> getResult() {

		return mWrappedResult;
	}

	@Override
	public String toString() {
		return mWrappedResult.toString();
	}

	private static class RabinWrapper<LETTER, PLACE> implements IRabinPetriNet<LETTER, PLACE> {
		final IPetriNet<LETTER, PLACE> mDifferenceNet;
		final Set<PLACE> mFinitePlaces;

		/**
		 *
		 * @param buchiPetriNet
		 *            a BuchiPetriNet that contains places from a RabinPetriNet
		 * @param rabinParent
		 *            a RabinPetriNet whose finite places should be finite in a derived BuchiPetriNet
		 */
		RabinWrapper(final IPetriNet<LETTER, PLACE> difference, final IRabinPetriNet<LETTER, PLACE> originalRabinNet) {
			mDifferenceNet = difference;
			mFinitePlaces = originalRabinNet.getFinitePlaces();
		}

		@Override
		public Set<PLACE> getPlaces() {
			return mDifferenceNet.getPlaces();
		}

		@Override
		public Set<Transition<LETTER, PLACE>> getTransitions() {
			return mDifferenceNet.getTransitions();
		}

		@Override
		public Set<PLACE> getAcceptingPlaces() {
			return mDifferenceNet.getAcceptingPlaces();
		}

		@Override
		public int flowSize() {
			return mDifferenceNet.flowSize();
		}

		@Override
		public Set<Transition<LETTER, PLACE>> getSuccessors(final PLACE place) {
			return mDifferenceNet.getSuccessors(place);
		}

		@Override
		public Set<Transition<LETTER, PLACE>> getPredecessors(final PLACE place) {
			return mDifferenceNet.getPredecessors(place);
		}

		@Override
		public Set<PLACE> getInitialPlaces() {
			return mDifferenceNet.getInitialPlaces();
		}

		@Override
		public boolean isAccepting(final Marking<PLACE> marking) {
			return mDifferenceNet.isAccepting(marking);
		}

		@Override
		public boolean isAccepting(final PLACE place) {
			return mDifferenceNet.isAccepting(place);
		}

		@Override
		public Set<LETTER> getAlphabet() {
			return mDifferenceNet.getAlphabet();
		}

		@Override
		public int size() {
			return mDifferenceNet.size();
		}

		@Override
		public String sizeInformation() {
			return mDifferenceNet.sizeInformation();
		}

		@Override
		public Set<PLACE> getFinitePlaces() {
			return mFinitePlaces;
		}

		@Override
		public boolean isFinite(final PLACE place) {
			return mFinitePlaces.contains(place);
		}

		@Override
		public String toString() {
			final StringBuilder result = new StringBuilder(mDifferenceNet.toString());
			result.insert(0, "Rabin");
			result.delete(result.lastIndexOf("}") + 1, result.length());
			result.append(",\n");
			result.append("finitePlaces = {");
			result.append(mFinitePlaces.toString());
			result.append("}\n);");
			return result.toString();
		}
	}

}
