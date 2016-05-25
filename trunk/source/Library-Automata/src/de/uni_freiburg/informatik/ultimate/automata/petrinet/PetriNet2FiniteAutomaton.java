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
package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;


/**
 * Given a PetriNet, constructs a finite Automaton that recognizes the same
 * language.
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <S> Symbol
 * @param <C> Content
 */
public class PetriNet2FiniteAutomaton<S,C> implements IOperation<S,C> {
	
	private final AutomataLibraryServices mServices;
    private final ILogger mLogger;
	
	private final IPetriNet<S, C> mNet;
	private final NestedWordAutomaton<S,C> mResult;

	
	@Override
	public String operationName() {
		return "petriNet2FiniteAutomaton";
	}
	
	@Override
	public String startMessage() {
		return "Start " + operationName() +
			"Operand " + mNet.sizeInformation();
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result " + 
				mResult.sizeInformation();
	}
	
	
	public PetriNet2FiniteAutomaton(AutomataLibraryServices services, 
			IPetriNet<S,C> net) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mNet = net;
		mLogger.info(startMessage());
		mContentFactory = net.getStateFactory();
		final Set<S> alphabet = new HashSet<S>(net.getAlphabet());
		mResult = new NestedWordAutomaton<S,C>(mServices, alphabet,
									 new HashSet<S>(0),
									 new HashSet<S>(0),
									 net.getStateFactory());
		getState(net.getInitialMarking(),true);
		while (!mWorklist.isEmpty()) {
			final Marking<S,C> marking = mWorklist.remove(0);
			constructOutgoingTransitions(marking);
		}
		mLogger.info(exitMessage());
	}
	
	
	
	/**
	 * List of markings for which
	 * <ul>
	 * <li> there has already been a state constructed
	 * <li> outgoing transitions of this state have not yet been constructed.
	 * </ul>
 
	 */
	private final List<Marking<S,C>> mWorklist = 
		new LinkedList<Marking<S,C>>();
	/**
	 * Maps a marking to the automaton state that represents this marking.
	 */
	Map<Marking<S,C>,C> mMarking2State =
		new HashMap<Marking<S,C>,C>();
	StateFactory<C> mContentFactory;


	
	
	/**
	 * Returns the automaton state that represents marking. If this state is not
	 * yet constructed, construct it and enqueue the marking. If it has to be
	 * constructed it is an initial state iff isInitial is true. 
	 */
	private C getState(Marking<S,C> marking, boolean isInitial) {
		C state = mMarking2State.get(marking);
		if (state == null) {
//			boolean isFinal = mNet.getAcceptingMarkings().contains(marking);
			final boolean isFinal = mNet.isAccepting(marking);
			state = mContentFactory.getContentOnPetriNet2FiniteAutomaton(marking);
			mResult.addState(isInitial, isFinal, state);
			mMarking2State.put(marking,state);
			mWorklist.add(marking);
		}
		return state;
	}
	
	private Collection<C> getMarkingContents(Set<Place<S,C>> marking) {
		final ArrayList<C> result = new ArrayList<C>(marking.size());
		for (final Place<S,C> place : marking) {
			result.add(place.getContent());
		}
		return result;
	}

	
	
	/**
	 * Given a marking. Get the state that represents the marking. Add all
	 * possible outgoing automaton transitions to state. Construct (and
	 * enqueue to worklist) successor states if necessary.
	 */
	private void constructOutgoingTransitions(Marking<S,C> marking) {
		final C state = getState(marking, false);
		final Set<ITransition<S,C>> outgoing = getOutgoingNetTransitions(marking);
		for (final ITransition<S,C> transition : outgoing) {
			if (marking.isTransitionEnabled(transition)) {
				final Marking<S,C> succMarking = marking.fireTransition(transition);
				final C succState = getState(succMarking, false);
				mResult.addInternalTransition(state, transition.getSymbol(),
																	succState);
				
			}
		}
		
	}
	
//	
//	private boolean isEnabled(ITransition<S,C> transition, 
//													Set<Place<S,C>> marking) {
//		if (marking.containsAll(transition.getPredecessors())) {
//			return true;
//		}
//		else return false;
//	}
	
	
	private Set<ITransition<S, C>> getOutgoingNetTransitions(
													Marking<S,C> marking) {
		final Set<ITransition<S,C>> transitions = new HashSet<ITransition<S,C>>();
		for (final Place<S,C> place : marking) {
			transitions.addAll(place.getSuccessors());
		}
		return transitions;
	}

	
	

	
	@Override
	public INestedWordAutomatonOldApi<S,C> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(StateFactory<C> stateFactory)
			throws AutomataLibraryException {
		return true;
	}



	
	
	

}
