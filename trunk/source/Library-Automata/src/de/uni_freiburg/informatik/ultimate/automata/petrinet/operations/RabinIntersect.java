package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * A class for intersecting a RabinPetriNet with a Buchi automaton
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            type of letters
 * @param <PLACE>
 *            type of places
 */
public class RabinIntersect<LETTER, PLACE>
		extends GeneralOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {

	RabinWrapper<LETTER, PLACE> mResult;

	/**
	 * Intersects the given @param{rabinPetriNet} with @param{buchiAutomaton}
	 *
	 * @param services
	 *            services
	 * @param factory
	 *            BlackWhiteStateFactory
	 * @param rabinPetriNet
	 *            rabinPetriNet
	 * @param buchiAutomaton
	 *            buchiAutomaton
	 */
	public RabinIntersect(final AutomataLibraryServices services, final IBlackWhiteStateFactory<PLACE> factory,
			final IRabinPetriNet<LETTER, PLACE> rabinPetriNet,
			final INestedWordAutomaton<LETTER, PLACE> buchiAutomaton) {
		super(services);

		mResult = new RabinWrapper<>(new BuchiIntersect<>(services, factory, rabinPetriNet, buchiAutomaton),
				rabinPetriNet);
	}

	@Override
	public IRabinPetriNet<LETTER, PLACE> getResult() {
		return mResult;
	}

	/**
	 * A wrapper for generating a RabinPetriNet using BuchiIntersect
	 *
	 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
	 *
	 * @param <LETTER>
	 *            type of letters
	 * @param <PLACE>
	 *            type of places
	 */
	private static class RabinWrapper<LETTER, PLACE> implements IRabinPetriNet<LETTER, PLACE> {
		final IPetriNet<LETTER, PLACE> mIntersectionNet;
		final HashSet<PLACE> mFinitePlaces = new HashSet<>();

		/**
		 *
		 * @param buchiPetriNet
		 *            a BuchiPetriNet that contains places from a RabinPetriNet
		 * @param rabinParent
		 *            a RabinPetriNet whose finite places should be finite in a derived BuchiPetriNet
		 */
		RabinWrapper(final BuchiIntersect<LETTER, PLACE> intersection,
				final IRabinPetriNet<LETTER, PLACE> originalRabinNet) {
			mIntersectionNet = intersection.getResult();
			for (final PLACE finitePlace : originalRabinNet.getFinitePlaces()) {
				final Pair<PLACE, PLACE> successors = intersection.getDerivedPlaces(finitePlace);
				mFinitePlaces.add(successors.getFirst());
				mFinitePlaces.add(successors.getSecond());
			}
		}

		@Override
		public Set<PLACE> getPlaces() {
			return mIntersectionNet.getPlaces();
		}

		@Override
		public Set<Transition<LETTER, PLACE>> getTransitions() {
			return mIntersectionNet.getTransitions();
		}

		@Override
		public Set<PLACE> getAcceptingPlaces() {
			return mIntersectionNet.getAcceptingPlaces();
		}

		@Override
		public int flowSize() {
			return mIntersectionNet.flowSize();
		}

		@Override
		public Set<Transition<LETTER, PLACE>> getSuccessors(final PLACE place) {
			return mIntersectionNet.getSuccessors(place);
		}

		@Override
		public Set<Transition<LETTER, PLACE>> getPredecessors(final PLACE place) {
			return mIntersectionNet.getPredecessors(place);
		}

		@Override
		public Set<PLACE> getInitialPlaces() {
			return mIntersectionNet.getInitialPlaces();
		}

		@Override
		public boolean isAccepting(final Marking<PLACE> marking) {
			return mIntersectionNet.isAccepting(marking);
		}

		@Override
		public boolean isAccepting(final PLACE place) {
			return mIntersectionNet.isAccepting(place);
		}

		@Override
		public Set<LETTER> getAlphabet() {
			return mIntersectionNet.getAlphabet();
		}

		@Override
		public int size() {
			return mIntersectionNet.size();
		}

		@Override
		public String sizeInformation() {
			return mIntersectionNet.sizeInformation();
		}

		@Override
		public Set<PLACE> getFinitePlaces() {
			return mFinitePlaces;
		}

		@Override
		public boolean isFinite(final PLACE place) {
			return mFinitePlaces.contains(place);
		}
	}

}
