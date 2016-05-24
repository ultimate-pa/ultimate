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
import java.util.LinkedList;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.ConcurrentProduct;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IsIncluded;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public class PrefixProduct<S,C> implements IOperation<S,C> {
	
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	
	private final PetriNetJulian<S,C> mNet;
	private final NestedWordAutomaton<S,C> mNwa;
	private PetriNetJulian<S,C> mResult;
	
	private HashSet<S> mNetOnlyAlphabet;
	private HashSet<S> mSharedAlphabet;
	private HashSet<S> mNwaOnlyAlphabet;
	private HashSet<S> mUnionAlphabet;
	
	private Map<Place<S,C>,Place<S,C>> oldPlace2newPlace = 
		new HashMap<Place<S,C>,Place<S,C>>();
	private Map<C,Place<S,C>> state2newPlace = 
		new HashMap<C,Place<S,C>>();
	
	private Map<S,Collection<ITransition<S,C>>> symbol2netTransitions = 
		new HashMap<S,Collection<ITransition<S,C>>>();
	private Map<S,Collection<AutomatonTransition>> symbol2nwaTransitions = 
		new HashMap<S,Collection<AutomatonTransition>>();
	
	
	@Override
	public String operationName() {
		return "prefixProduct";
	}
	
	@Override
	public String startMessage() {
		return "Start " + operationName() +
			"First Operand " + mNet.sizeInformation() +
			"Second Operand " + mNwa.sizeInformation();
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() +
			" Result " + mResult.sizeInformation();
	}
	
	
	
	
	
	private void updateSymbol2netTransitions(S symbol, 
											 ITransition<S,C> netTransition) {
		Collection<ITransition<S,C>> netTransitions;
		netTransitions = symbol2netTransitions.get(symbol);
		if (netTransitions == null) {
			netTransitions = new LinkedList<ITransition<S,C>>();
			symbol2netTransitions.put(symbol, netTransitions);
		}
		netTransitions.add(netTransition);
	}
	
	private void updateSymbol2nwaTransitions(S symbol, 
				AutomatonTransition nwaTransition) {
		Collection<AutomatonTransition> nwaTransitions;
		nwaTransitions = symbol2nwaTransitions.get(symbol);
		if (nwaTransitions == null) {
			nwaTransitions = new LinkedList<AutomatonTransition>();
			symbol2nwaTransitions.put(symbol, nwaTransitions);
		}
		nwaTransitions.add(nwaTransition);
	}
	

	
	public PrefixProduct(AutomataLibraryServices services,
			PetriNetJulian<S, C> net, NestedWordAutomaton<S, C> nwa) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		this.mNet = net;
		this.mNwa = nwa;
		if (nwa.getInitialStates().size() != 1) {
			throw new UnsupportedOperationException("PrefixProduct needs an" +
					" automaton with exactly one inital state");
		}
		computeResult();
	}
	
	public PetriNetJulian<S,C> getResult() throws AutomataLibraryException {
		return this.mResult;
	}
	
	
	private void computeResult() {
		mNetOnlyAlphabet = new HashSet<S>(mNet.getAlphabet());
		mNetOnlyAlphabet.removeAll(mNwa.getInternalAlphabet());
		mSharedAlphabet = new HashSet<S>(mNet.getAlphabet());
		mSharedAlphabet.removeAll(mNetOnlyAlphabet);
		mNwaOnlyAlphabet = new HashSet<S>(mNwa.getInternalAlphabet());
		mNwaOnlyAlphabet.removeAll(mSharedAlphabet);
		mUnionAlphabet = new HashSet<S>(mNet.getAlphabet());
		mUnionAlphabet.addAll(mNwaOnlyAlphabet);

		// prefix product preserves the constantTokenAmount invariant
		final boolean constantTokenAmount = mNet.constantTokenAmount();
		mResult = new PetriNetJulian<S,C>(mServices, mUnionAlphabet, 
										 mNet.getStateFactory(),
										 constantTokenAmount);
		
		//add places of old net
		for (Place<S,C> oldPlace : mNet.getPlaces()) {
			C content = oldPlace.getContent();
			boolean isInitial = mNet.getInitialMarking().contains(oldPlace);
			boolean isAccepting = mNet.getAcceptingPlaces().contains(oldPlace);
			Place<S,C> newPlace = mResult.addPlace(content, isInitial, isAccepting);
			oldPlace2newPlace.put(oldPlace, newPlace);
		}
		
		//add states of automaton
		for (C state : mNwa.getStates()) {
			C content = state;
			boolean isInitial = mNwa.getInitialStates().contains(state);
			boolean isAccepting = mNwa.isFinal(state);
			Place<S,C> newPlace = mResult.addPlace(content, isInitial, isAccepting);
			state2newPlace.put(state, newPlace);
		}
		
		for (ITransition<S,C> trans : mNet.getTransitions()) {
			updateSymbol2netTransitions(trans.getSymbol(), trans);
		}
		
		for (C state : mNwa.getStates()) {
			for (S letter : mNwa.lettersInternal(state)) {
				for (C succ : mNwa.succInternal(state, letter)) {
					Collection<AutomatonTransition> automatonTransitions = 
							symbol2nwaTransitions.get(letter);
					if (automatonTransitions == null) {
						automatonTransitions = new HashSet<AutomatonTransition>();
						symbol2nwaTransitions.put(letter, automatonTransitions);
					}
					automatonTransitions.add(
							new AutomatonTransition(state, letter, succ));
				}
			}
		}
		
		for (S symbol : mNetOnlyAlphabet) {
			for (ITransition<S,C> trans : symbol2netTransitions.get(symbol)) {
				Collection<Place<S,C>> predecessors = 
											new ArrayList<Place<S,C>>();
				for (Place<S,C> oldPlace : trans.getPredecessors()) {
					Place<S,C> newPlace = oldPlace2newPlace.get(oldPlace);
					predecessors.add(newPlace);
				}
				Collection<Place<S,C>> successors = 
					new ArrayList<Place<S,C>>();
				for (Place<S,C> oldPlace : trans.getSuccessors()) {
					Place<S,C> newPlace = oldPlace2newPlace.get(oldPlace);
					successors.add(newPlace);
				}
				mResult.addTransition(trans.getSymbol(), predecessors, successors);
			}
		}
		
		for (S symbol : mNwaOnlyAlphabet) {
			for (AutomatonTransition trans : 
											symbol2nwaTransitions.get(symbol)) {
				Collection<Place<S,C>> predecessors = 
											new ArrayList<Place<S,C>>(1);
				{
					Place<S,C> newPlace = 
						state2newPlace.get(trans.getPredecessor());
					predecessors.add(newPlace);
				}
				
				Collection<Place<S,C>> successors = 
											new ArrayList<Place<S,C>>(1);
				{
					Place<S,C> newPlace = 
						state2newPlace.get(trans.getSuccessor());
					successors.add(newPlace);
				}
				mResult.addTransition(trans.getSymbol(), predecessors, successors);
			}
		}
		
		for (S symbol : mSharedAlphabet) {
			if (symbol2netTransitions.containsKey(symbol))
			for (ITransition<S,C> netTrans : symbol2netTransitions.get(symbol)) {
				if (symbol2nwaTransitions.containsKey(symbol))		
				for (AutomatonTransition nwaTrans : 
											symbol2nwaTransitions.get(symbol)) {
				
				Collection<Place<S,C>> predecessors = 
											new ArrayList<Place<S,C>>();
				for (Place<S,C> oldPlace : netTrans.getPredecessors()) {
					Place<S,C> newPlace = oldPlace2newPlace.get(oldPlace);
					predecessors.add(newPlace);
				}
				predecessors.add(state2newPlace.get(nwaTrans.getPredecessor()));
				
				
				Collection<Place<S,C>> successors = 
					new ArrayList<Place<S,C>>();
				for (Place<S,C> oldPlace : netTrans.getSuccessors()) {
					Place<S,C> newPlace = oldPlace2newPlace.get(oldPlace);
					successors.add(newPlace);
				}
				successors.add(state2newPlace.get(nwaTrans.getSuccessor()));
				mResult.addTransition(netTrans.getSymbol(), predecessors, successors);
				
				}
			}
		}
	}

	private class AutomatonTransition {
		private final C predecessor;
		private final S letter;
		private final C successor;

		public AutomatonTransition(C predecessor, S letter, C successor) {
			this.predecessor = predecessor;
			this.letter = letter;
			this.successor = successor;
		}

		public C getPredecessor() {
			return predecessor;
		}

		public S getSymbol() {
			return letter;
		}

		public C getSuccessor() {
			return successor;
		}
		
		
	}

	@Override
	public boolean checkResult(StateFactory<C> stateFactory)
			throws AutomataLibraryException {
		mLogger.info("Testing correctness of prefixProduct");

		INestedWordAutomatonOldApi op1AsNwa = (new PetriNet2FiniteAutomaton(mServices, mNet)).getResult();
		INestedWordAutomatonOldApi resultAsNwa = (new PetriNet2FiniteAutomaton(mServices, mResult)).getResult();
		INestedWordAutomatonOldApi nwaResult = (new ConcurrentProduct(mServices, op1AsNwa, mNwa, true)).getResult();
		boolean correct = true;
		correct &= (new IsIncluded(mServices, stateFactory, resultAsNwa,nwaResult)).getResult();
		correct &= (new IsIncluded(mServices, stateFactory, nwaResult,resultAsNwa)).getResult();

		mLogger.info("Finished testing correctness of prefixProduct");
		return correct;
	}
	
}
