/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEquivalent;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DifferenceDD;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Computes the difference between a {@link PetriNetJulian} and a {@link NestedWordAutomaton}.
 * <p>
 * TODO Christian 2016-09-06: If the <tt>finalIsTrap</tt> method is removed, the input can become an
 * {@link INestedWordAutomaton}.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <S>
 *            symbol type
 * @param <C>
 *            content type
 */
public final class DifferenceBlackAndWhite<S, C> extends UnaryNetOperation<S, C> {
	private final PetriNetJulian<S, C> mOperand;
	private final INestedWordAutomaton<S, C> mNwa;
	private final IBlackWhiteStateFactory<C> mContentFactory;
	
	private PetriNetJulian<S, C> mResult;
	
	private final Map<Place<S, C>, Place<S, C>> mOldPlace2NewPlace = new HashMap<>();
	
	private final Map<S, Set<C>> mSelfloop = new HashMap<>();
	private final Map<S, Set<C>> mStateChanger = new HashMap<>();
	
	private final Map<C, Place<S, C>> mWhitePlace = new HashMap<>();
	
	private final Map<C, Place<S, C>> mBlackPlace = new HashMap<>();
	
	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param factory
	 *            content factory
	 * @param net
	 *            Petri net
	 * @param nwa
	 *            nested word automaton
	 */
	public <FACTORY extends IBlackWhiteStateFactory<C> & ISinkStateFactory<C>> DifferenceBlackAndWhite(
			final AutomataLibraryServices services, final FACTORY factory, final PetriNetJulian<S, C> net,
			final NestedWordAutomaton<S, C> nwa) {
		super(services);
		mOperand = net;
		mNwa = nwa;
		mContentFactory = factory;
		
		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}
		
		if (!IAutomaton.sameAlphabet(net, nwa)) {
			throw new IllegalArgumentException("net and nwa must use same alphabet");
		}
		if (nwa.getInitialStates().size() != 1) {
			throw new UnsupportedOperationException(
					"DifferenceBlackAndWhite needs an automaton with exactly one inital state");
		}
		final C nwaInitialState = nwa.getInitialStates().iterator().next();
		classifySymbols();
		// mSymbol2AutomatonTransition = createSymbol2AutomatonTransitionMap();
		if (nwa.isFinal(nwaInitialState)) {
			// case where nwa accepts everything. Result will be a net that
			// accepts the empty language
			mResult = new PetriNetJulian<>(mServices, mOperand.getAlphabet(), mOperand.getStateFactory(), true);
			final C sinkContent = factory.createSinkStateContent();
			mResult.addPlace(sinkContent, true, false);
		} else {
			copyNetStatesOnly();
			addBlackAndWhitePlaces();
			addTransitions();
		}
		
		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}
	
	@Override
	public String operationName() {
		return "DifferenceBlackAndWhite";
	}
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + "First Operand " + mOperand.sizeInformation() + "Second Operand "
				+ mNwa.sizeInformation();
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". Result " + mResult.sizeInformation();
	}
	
	private void classifySymbols() {
		for (final S symbol : mNwa.getInternalAlphabet()) {
			final HashSet<C> selfloopStates = new HashSet<>();
			final HashSet<C> changerStates = new HashSet<>();
			for (final C state : mNwa.getStates()) {
				if (mNwa.isFinal(state)) {
					// we do not consider accepting states since they
					// do not occur in the result anyway
					continue;
				}
				
				final Iterator<OutgoingInternalTransition<S, C>> successorsIt =
						mNwa.internalSuccessors(state, symbol).iterator();
				if (!successorsIt.hasNext()) {
					continue;
				}
				@SuppressWarnings("squid:S1941")
				final C succState = successorsIt.next().getSucc();
				if (successorsIt.hasNext()) {
					throw new IllegalArgumentException("Only deterministic automata supported");
				}
				if (succState.equals(state)) {
					selfloopStates.add(state);
				} else {
					changerStates.add(state);
				}
			}
			mSelfloop.put(symbol, selfloopStates);
			mStateChanger.put(symbol, changerStates);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(symbol + " " + selfloopStates.size() + " times selfloop " + changerStates.size()
						+ " times changer");
			}
		}
	}
	
	/*
	private Map<S,Set<NestedWordAutomaton<S,C>.InternalTransition>> createSymbol2AutomatonTransitionMap() {
		Map<S,Set<NestedWordAutomaton<S,C>.InternalTransition>> result =
			new HashMap<S,Set<NestedWordAutomaton<S,C>.InternalTransition>>();
		for (NestedWordAutomaton<S,C>.InternalTransition trans : mNwa.getInternalTransitions()) {
			S symbol = trans.getSymbol();
			Set<NestedWordAutomaton<S,C>.InternalTransition> transitions =
				result.get(symbol);
			if (transitions == null) {
				transitions = new HashSet<NestedWordAutomaton<S,C>.InternalTransition>();
				result.put(symbol,transitions);
			}
			transitions.add(trans);
		}
		return result;
	}
	
	private Map<S, Set<ITransition<S, C>>> createSymbol2TransitionMap(
			PetriNetJulian<S, C> net) {
		Map<S, Set<ITransition<S, C>>> result =
				new HashMap<S, Set<ITransition<S, C>>>();
		for (S symbol : net.getAlphabet()) {
			result.put(symbol, new HashSet<ITransition<S, C>>());
		}
		for (ITransition<S, C> transition : net.getTransitions()) {
			result.get(transition.getSymbol()).add(transition);
		}
		return result;
	}
	*/
	
	private void copyNetStatesOnly() {
		// difference black and white preserves the constantTokenAmount invariant
		final boolean constantTokenAmount = mOperand.constantTokenAmount();
		mResult = new PetriNetJulian<>(mServices, mOperand.getAlphabet(), mOperand.getStateFactory(),
				constantTokenAmount);
		
		for (final Place<S, C> oldPlace : mOperand.getPlaces()) {
			final C content = oldPlace.getContent();
			final boolean isInitial = mOperand.getInitialMarking().contains(oldPlace);
			final boolean isAccepting = mOperand.getAcceptingPlaces().contains(oldPlace);
			final Place<S, C> newPlace = mResult.addPlace(content, isInitial, isAccepting);
			mOldPlace2NewPlace.put(oldPlace, newPlace);
		}
	}
	
	private void addBlackAndWhitePlaces() {
		for (final C state : mNwa.getStates()) {
			if (!mNwa.isFinal(state)) {
				final boolean isInitial = mNwa.getInitialStates().contains(state);
				final C stateContent = state;
				final C whiteContent = mContentFactory.getWhiteContent(stateContent);
				final Place<S, C> whitePlace = mResult.addPlace(whiteContent, isInitial, false);
				mWhitePlace.put(state, whitePlace);
				final C blackContent = mContentFactory.getBlackContent(stateContent);
				final Place<S, C> blackPlace = mResult.addPlace(blackContent, !isInitial, false);
				mBlackPlace.put(state, blackPlace);
			}
		}
	}
	
	private void addTransitions() {
		for (final ITransition<S, C> oldTrans : mOperand.getTransitions()) {
			final S symbol = oldTrans.getSymbol();
			
			// A copy for each changer
			for (final C predState : mStateChanger.get(symbol)) {
				final Iterator<OutgoingInternalTransition<S, C>> succStatesIt =
						mNwa.internalSuccessors(predState, symbol).iterator();
				assert succStatesIt.hasNext();
				final C succState = succStatesIt.next().getSucc();
				assert !succStatesIt.hasNext();
				
				// omit transitions to final states
				if (mNwa.isFinal(succState)) {
					continue;
				}
				
				final Collection<Place<S, C>> predecessors = new ArrayList<>();
				for (final Place<S, C> oldPlace : oldTrans.getPredecessors()) {
					final Place<S, C> newPlace = mOldPlace2NewPlace.get(oldPlace);
					predecessors.add(newPlace);
				}
				assert mWhitePlace.containsKey(predState);
				predecessors.add(mWhitePlace.get(predState));
				assert mWhitePlace.containsKey(succState);
				predecessors.add(mBlackPlace.get(succState));
				
				final Collection<Place<S, C>> successors = new ArrayList<>();
				for (final Place<S, C> oldPlace : oldTrans.getSuccessors()) {
					final Place<S, C> newPlace = mOldPlace2NewPlace.get(oldPlace);
					successors.add(newPlace);
				}
				assert mWhitePlace.containsKey(succState);
				successors.add(mWhitePlace.get(succState));
				assert mBlackPlace.containsKey(predState);
				successors.add(mBlackPlace.get(predState));
				
				mResult.addTransition(oldTrans.getSymbol(), predecessors, successors);
			}
			
			// One copy for the selfloops
			if (!mSelfloop.isEmpty()) {
				/*
				Collection<IState<S,C>> succStates = predState.getInternalSucc(symbol);
				assert (succStates.size() == 1);
				IState<S,C> succState = succStates.iterator().next();
				*/
				final Collection<Place<S, C>> predecessors = new ArrayList<>();
				for (final Place<S, C> oldPlace : oldTrans.getPredecessors()) {
					final Place<S, C> newPlace = mOldPlace2NewPlace.get(oldPlace);
					predecessors.add(newPlace);
				}
				/*
				predecessors.add(mWhitePlace.get(predState));
				predecessors.add(mBlackPlace.get(succState));
				*/
				
				final Collection<Place<S, C>> successors = new ArrayList<>();
				for (final Place<S, C> oldPlace : oldTrans.getSuccessors()) {
					final Place<S, C> newPlace = mOldPlace2NewPlace.get(oldPlace);
					successors.add(newPlace);
				}
				/*
				successors.add(mWhitePlace.get(succState));
				successors.add(mBlackPlace.get(predState));
				*/
				
				for (final C state : mStateChanger.get(symbol)) {
					predecessors.add(mBlackPlace.get(state));
					successors.add(mBlackPlace.get(state));
				}
				
				mResult.addTransition(oldTrans.getSymbol(), predecessors, successors);
			}
		}
	}
	
	/*
	private IState<S, C> getSuccessorState(IState<S, C> state, S symbol) {
		Collection<IState<S, C>> successors = state.getInternalSucc(symbol);
		if (successors.size() > 1) {
			throw new IllegalArgumentException(
					"Only deterministic automata supported");
		}
		for (IState<S, C> succ : successors) {
			return succ;
		}
		return null;
	}
	*/
	
	@Override
	protected IPetriNet<S, C> getOperand() {
		return mOperand;
	}
	
	@Override
	public PetriNetJulian<S, C> getResult() {
		assert isPreSuccPlaceInNet(mResult);
		assert isPreSuccTransitionInNet(mResult);
		return mResult;
	}
	
	private boolean isPreSuccPlaceInNet(final PetriNetJulian<S, C> net) {
		for (final ITransition<S, C> trans : net.getTransitions()) {
			for (final Place<S, C> place : trans.getPredecessors()) {
				if (!net.getPlaces().contains(place)) {
					return false;
				}
			}
			for (final Place<S, C> place : trans.getSuccessors()) {
				if (!net.getPlaces().contains(place)) {
					return false;
				}
			}
		}
		return true;
	}
	
	private boolean isPreSuccTransitionInNet(final PetriNetJulian<S, C> net) {
		for (final Place<S, C> place : net.getPlaces()) {
			for (final ITransition<S, C> trans : place.getPredecessors()) {
				if (!net.getTransitions().contains(trans)) {
					return false;
				}
			}
			for (final ITransition<S, C> trans : place.getSuccessors()) {
				if (!net.getTransitions().contains(trans)) {
					return false;
				}
			}
		}
		return true;
	}
	
	@Override
	public boolean checkResult(final IStateFactory<C> stateFactory) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Testing correctness of " + operationName());
		}
		
		// TODO Christian 2017-02-15 Casts are temporary workarounds until state factory becomes class parameter
		final INestedWordAutomatonSimple<S, C> op1AsNwa = (new PetriNet2FiniteAutomaton<>(mServices,
				(IPetriNet2FiniteAutomatonStateFactory<C>) stateFactory, mOperand)).getResult();
		final INestedWordAutomatonSimple<S, C> rcResult = (new DifferenceDD<>(mServices,
				(IDeterminizeStateFactory<C> & IIntersectionStateFactory<C>) stateFactory, op1AsNwa, mNwa)).getResult();
		final INestedWordAutomatonSimple<S, C> resultAsNwa = (new PetriNet2FiniteAutomaton<>(mServices,
				(IPetriNet2FiniteAutomatonStateFactory<C>) stateFactory, mResult)).getResult();
		
		boolean correct = true;
		correct &= new IsEquivalent<>(mServices,
				(ISinkStateFactory<C> & IDeterminizeStateFactory<C> & IIntersectionStateFactory<C> & IEmptyStackStateFactory<C>) stateFactory,
				resultAsNwa, rcResult).getResult();
		
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of " + operationName());
		}
		return correct;
	}
}
