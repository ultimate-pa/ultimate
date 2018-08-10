package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.ISuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

public class DifferencePetriNet<LETTER, PLACE> implements IPetriNetSuccessorProvider<LETTER, PLACE> {

	private static final String EXACTLY_ONE_STATE_OF_SUBTRAHEND = "query for successors must contain exactly one state of subtrahend";
	private static final String EMPTY_INITIAL_ERROR_MESSAGE = "Subtrahend has no initial states! We could soundly return the minuend as result (implement this if required). However we presume that in most cases, such a subtrahend was passed accidentally";
	private final AutomataLibraryServices mServices;
	private final IPetriNetSuccessorProvider<LETTER, PLACE> mMinued;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> mSubtrahend;
	private final Map<ITransition<LETTER, PLACE>, ITransition<LETTER, PLACE>> mNew2Old = new HashMap<ITransition<LETTER,PLACE>, ITransition<LETTER,PLACE>>();
	private final HashRelation<ITransition<LETTER, PLACE>, ITransition<LETTER, PLACE>> mOld2New = new HashRelation<>();
	private final Map<ITransition<LETTER, PLACE>, PLACE> mNewTransition2AutomatonPredecessorState = new HashMap<>();
	private final Set<PLACE> mMinuendPlaces = new HashSet<>();
	private final Set<PLACE> mSubtrahendStates = new HashSet<>();
	private final NestedMap2<ITransition<LETTER, PLACE>, PLACE, ITransition<LETTER, PLACE>> mInputTransition2State2OutputTransition = new NestedMap2<>();
	private int mNumberOfConstructedTransitions = 0;
	private final Map<ITransition<LETTER, PLACE>, Transition<LETTER, PLACE>> mTransitions = new HashMap<>();




	public DifferencePetriNet(final AutomataLibraryServices services, final IPetriNetSuccessorProvider<LETTER, PLACE> minued,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> subtrahend) {
		super();
		mServices = services;
		mMinued = minued;
		mSubtrahend = subtrahend;
	}

	@Override
	public Set<PLACE> getInitialPlaces() {
		final Set<PLACE> result = new HashSet<>(mMinued.getInitialPlaces());
		final Iterator<PLACE> it = mSubtrahend.getInitialStates().iterator();
		if (!it.hasNext()) {
			throw new UnsupportedOperationException(
					EMPTY_INITIAL_ERROR_MESSAGE);
		}
		final PLACE automatonInitialState = it.next();
		result.add(automatonInitialState);
		if (it.hasNext()) {
			throw new IllegalArgumentException("subtrahend not deterministic");
		}
		if (mSubtrahend.isFinal(automatonInitialState)) {
			return Collections.emptySet();
		}
		mSubtrahendStates.add(automatonInitialState);
		for (final PLACE initialPlace : mMinued.getInitialPlaces()) {
			mMinuendPlaces.add(initialPlace);
		}
		return result;
	}

	@Override
	public Set<PLACE> getSuccessors(final ITransition<LETTER, PLACE> transition) {
		final Transition<LETTER, PLACE> casted = mTransitions.get(transition);
		if (casted == null) {
			throw new IllegalArgumentException("unknown transition " + transition);
		} else {
			return casted.getSuccessors();
		}
	}

	@Override
	public Set<PLACE> getPredecessors(final ITransition<LETTER, PLACE> transition) {
		final Transition<LETTER, PLACE> casted = mTransitions.get(transition);
		if (casted == null) {
			throw new IllegalArgumentException("unknown transition " + transition);
		} else {
			return casted.getPredecessors();
		}
	}


	/**
	 * @param places
	 *            Set of places where exactly one is a state of the subtrahend and the others are places of the minuend.
	 */
	@Override
	public Collection<ISuccessorTransitionProvider<LETTER, PLACE>> getSuccessorTransitionProviders(
			final Collection<PLACE> places) {
		if (places.isEmpty()) {
			return Collections.emptySet();
		}
		PLACE automatonPredecessor = null;
		final List<PLACE> petriNetPredecessors = new ArrayList<>();
		for (final PLACE place : places) {
			if (mMinuendPlaces.contains(place)) {
				petriNetPredecessors.add(place);
			} else if (mSubtrahendStates.contains(place)) {
				if (automatonPredecessor == null) {
					automatonPredecessor = place;
				} else {
					throw new IllegalArgumentException(EXACTLY_ONE_STATE_OF_SUBTRAHEND);
				}
			}
		}
		if (automatonPredecessor == null) {
			throw new IllegalArgumentException(EXACTLY_ONE_STATE_OF_SUBTRAHEND);
		}
		final List<ISuccessorTransitionProvider<LETTER, PLACE>> result = new ArrayList<>();
		// do use transitions of *all* yet known places because the subtrahend
		// predecessor could potentially have a transition with all of them.
		final Collection<ISuccessorTransitionProvider<LETTER, PLACE>> preds = mMinued.getSuccessorTransitionProviders(mMinuendPlaces);
		for (final ISuccessorTransitionProvider<LETTER, PLACE> pred : preds) {
			result.add(new DifferenceSuccessorTransitionProvider(pred, automatonPredecessor));
		}
		return result;
	}

	@Override
	public boolean isAccepting(final Marking<LETTER, PLACE> marking) {
		final Set<PLACE> petriNetPlaces = new HashSet<>();
		for (final PLACE place : marking) {
			if (mMinuendPlaces.contains(place)) {
				petriNetPlaces.add(place);
			}
		}
		final Marking<LETTER, PLACE> filteredMarking = new Marking<>(petriNetPlaces);
		return mMinued.isAccepting(filteredMarking);
	}

	private class DifferenceSuccessorTransitionProvider implements ISuccessorTransitionProvider<LETTER, PLACE> {
		private final ISuccessorTransitionProvider<LETTER, PLACE> mPetriNetPredecessors;
		private final PLACE mAutomatonPredecessor;
		private final LinkedHashSet<PLACE> mAllPredecessors;

		public DifferenceSuccessorTransitionProvider(
				final ISuccessorTransitionProvider<LETTER, PLACE> petriNetPredecessors,
				final PLACE automatonPredecessor) {
			super();
			mPetriNetPredecessors = petriNetPredecessors;
			mAutomatonPredecessor = automatonPredecessor;
			mAllPredecessors = new LinkedHashSet<>(petriNetPredecessors.getPredecessorPlaces());
			mAllPredecessors.add(automatonPredecessor);
		}

		@Override
		public Set<PLACE> getPredecessorPlaces() {
			return Collections.unmodifiableSet(mAllPredecessors);
		}

		@Override
		public Collection<ITransition<LETTER, PLACE>> getTransitions() {
			final List<ITransition<LETTER, PLACE>> result = new ArrayList<>();
			for (final ITransition<LETTER, PLACE> inputTransition : mPetriNetPredecessors.getTransitions()) {
				final ITransition<LETTER, PLACE> outputTransition = getOrConstructTransition(inputTransition, mAutomatonPredecessor);
				if (outputTransition != null) {
					result.add(outputTransition);
				}
			}
			return result;
		}

		/**
		 *
		 * @return null iff subtrahend successor is accepting which means that we do not
		 *         want such a transition in our resulting Petri net.
		 */
		private ITransition<LETTER, PLACE> getOrConstructTransition(final ITransition<LETTER, PLACE> inputTransition,
				final PLACE automatonPredecessor) {
			ITransition<LETTER, PLACE> result = mInputTransition2State2OutputTransition.get(inputTransition, automatonPredecessor);
			if (result == null) {
				OutgoingInternalTransition<LETTER, PLACE> subtrahendSucc;
				{
					final Iterable<OutgoingInternalTransition<LETTER, PLACE>> subtrahendSuccs = mSubtrahend.internalSuccessors(automatonPredecessor, inputTransition.getSymbol());
					final Iterator<OutgoingInternalTransition<LETTER, PLACE>> it = subtrahendSuccs.iterator();
					if (!it.hasNext()) {
						throw new IllegalArgumentException("Subtrahend not total.");
					}
					subtrahendSucc = it.next();
					if (it.hasNext()) {
						throw new IllegalArgumentException("Subtrahend not deterministic.");
					}
				}
				if (mSubtrahend.isFinal(subtrahendSucc.getSucc())) {
					return null;
				} else {
					final Set<PLACE> successors = new LinkedHashSet<>();
					for (final PLACE petriNetSuccessor : mMinued.getSuccessors(inputTransition)) {
						// possibly first time that we saw this place, add
						mMinuendPlaces.add(petriNetSuccessor);
						successors.add(petriNetSuccessor);
					}
					mSubtrahendStates.add(subtrahendSucc.getSucc());
					successors.add(subtrahendSucc.getSucc());

				final int totalOrderId = mNumberOfConstructedTransitions;
				mNumberOfConstructedTransitions++;
				result = new Transition<>(inputTransition.getSymbol(), mAllPredecessors, successors, totalOrderId);
				mInputTransition2State2OutputTransition.put(inputTransition, automatonPredecessor, result);
				mTransitions.put(result, (Transition<LETTER, PLACE>) result);
				}
			}
			return result;
		}
	}

	BoundedPetriNet<LETTER, PLACE> getYetConstructedPetriNet() {
		final BoundedPetriNet<LETTER, PLACE> result = new BoundedPetriNet<>(mServices, mMinued.getAlphabet(), false);
		for (final PLACE place : mMinuendPlaces) {
			result.addPlace(place, mMinued.getInitialPlaces().contains(place), mMinued.isAccepting(place));
		}
		for (final PLACE place : mSubtrahendStates) {
			result.addPlace(place, mSubtrahend.isInitial(place), false);
		}
		for (final Entry<ITransition<LETTER, PLACE>, Transition<LETTER, PLACE>> entry : mTransitions.entrySet()) {
			result.addTransition(entry.getValue().getSymbol(), entry.getValue().getPredecessors(), entry.getValue().getSuccessors());
		}
		return result;

	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mMinued.getAlphabet();
	}

	@Override
	public int size() {
		// TODO Auto-generated method stub
		return -1;
	}

	@Override
	public String sizeInformation() {
		// TODO Auto-generated method stub
		return "not available";
	}

	@Override
	public IElement transformToUltimateModel(final AutomataLibraryServices services)
			throws AutomataOperationCanceledException {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isAccepting(final PLACE place) {
		if (mSubtrahendStates.contains(place)) {
			return false;
		} else {
			return mMinued.isAccepting(place);
		}
	}

}
