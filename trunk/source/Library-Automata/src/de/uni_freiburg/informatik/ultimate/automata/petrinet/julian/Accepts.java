/*
 * Copyright (C) 2011-2015 Julian Jarecki (jareckij@informatik.uni-freiburg.de)
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

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

public class Accepts<S, C>
		extends UnaryNetOperation<S, C>
		implements IOperation<S, C> {
	
	private final Word<S> mWord;
	private final Boolean mResult;
	
	/**
	 * Constructor.
	 * 
	 * @param services Ultimate services
	 * @param net Petri net
	 * @param word word
	 * @throws AutomataLibraryException if construction fails
	 */
	public Accepts(final AutomataLibraryServices services,
			final IPetriNet<S, C> net, final Word<S> word)
					throws AutomataLibraryException {
		super(services, net);
		mWord = word;
		mLogger.info(startMessage());
		// this.marking = new HashSet<Place<S, C>>(net.getInitialMarking());
		// this.position = 0;
		mResult = getResultHelper(0,net.getInitialMarking());
		mLogger.info(exitMessage());
	}
	
	@Override
	public String operationName() {
		return "acceptsJulian";
	}

	// private Collection<Place<S, C>> marking;
	// private int position;
	
	@Override
	public String startMessage() {
		return "Start " + operationName()
			+ "Operand " + mOperand.sizeInformation();
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}

	private boolean getResultHelper(int position,
	        final Marking<S, C> marking) throws AutomataLibraryException {
		if (position >= mWord.length()) {
			return mOperand.isAccepting(marking);
		}
		
		
		if (isCancellationRequested()) {
			throw new AutomataOperationCanceledException(this.getClass());
		}

		final S symbol = mWord.getSymbol(position);
		if (!mOperand.getAlphabet().contains(symbol)) {
			throw new IllegalArgumentException("Symbol " + symbol
					+ " not in alphabet");
		}

		final HashSet<ITransition<S, C>> activeTransitionsWithTheSymbol =
											new HashSet<ITransition<S, C>>();

		// get all active transitions which are labeled with the next symbol
		for (final Place<S, C> place : marking) {
			for (final ITransition<S, C> transition : place.getSuccessors()) {
				if (marking.isTransitionEnabled(transition)
				        && transition.getSymbol().equals(symbol)) {
					activeTransitionsWithTheSymbol.add(transition);
				}
			}
		}
		// marking = new HashSet<Place<S,C>>();
		position++;
		boolean result = false;
		Marking<S, C> nextMarking;
		for (final ITransition<S, C> transition : activeTransitionsWithTheSymbol) {
			nextMarking = marking.fireTransition(transition);
			if (getResultHelper(position, nextMarking)) {
				result = true;
			}
		}
		return result;
	}

	@Override
	public boolean checkResult(final IStateFactory<C> stateFactory)
			throws AutomataLibraryException {

		mLogger.info("Testing correctness of accepts");

		final NestedWord<S> nw = NestedWord.nestedWord(mWord);
		final boolean resultAutomata =
				(new de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts<S, C>(
						mServices,
						(new PetriNet2FiniteAutomaton<S, C>(mServices, mOperand)).getResult(),
						nw)).getResult();
		final boolean correct = (mResult == resultAutomata);

		mLogger.info("Finished testing correctness of accepts");

		return correct;
	}
}
