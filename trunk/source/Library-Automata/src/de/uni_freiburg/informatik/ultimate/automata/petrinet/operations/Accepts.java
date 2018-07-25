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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Place;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;

/**
 * Acceptance test for Petri nets.
 * 
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <S>
 *            symbol type
 * @param <C>
 *            place content type
 */
public final class Accepts<S, C> extends UnaryNetOperation<S, C, IPetriNet2FiniteAutomatonStateFactory<C>> {
	private final IPetriNet<S, C> mOperand;
	private final Word<S> mWord;
	private final boolean mResult;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            Petri net
	 * @param word
	 *            word
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public Accepts(final AutomataLibraryServices services, final IPetriNet<S, C> operand, final Word<S> word)
			throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		mWord = word;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		// this.marking = new HashSet<Place<C>>(net.getInitialMarking());
		// this.position = 0;
		mResult = getResultHelper(0, operand.getInitialMarking());

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	// private Collection<Place<C>> marking;
	// private int position;

	@Override
	public String startMessage() {
		return "Start " + getOperationName() + ". Operand " + mOperand.sizeInformation();
	}

	@Override
	protected IPetriNet<S, C> getOperand() {
		return mOperand;
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}

	private boolean getResultHelper(final int position, final Marking<S, C> marking)
			throws AutomataOperationCanceledException {
		if (position >= mWord.length()) {
			return mOperand.isAccepting(marking);
		}

		if (isCancellationRequested()) {
			throw new AutomataOperationCanceledException(this.getClass());
		}

		final S symbol = mWord.getSymbol(position);
		if (!mOperand.getAlphabet().contains(symbol)) {
			throw new IllegalArgumentException("Symbol " + symbol + " not in alphabet");
		}

		final int nextPosition = position + 1;
		boolean result = false;
		Marking<S, C> nextMarking;
		for (final ITransition<S, C> transition : activeTransitionsWithSymbol(marking, symbol)) {
			nextMarking = marking.fireTransition(transition);
			if (getResultHelper(nextPosition, nextMarking)) {
				result = true;
			}
		}
		return result;
	}

	private Set<ITransition<S, C>> activeTransitionsWithSymbol(Marking<S, C> marking, S symbol) {
		final Set<ITransition<S, C>> activeTransitionsWithSymbol = new HashSet<>();
		for (final Place<C> place : marking) {
			mOperand.getSuccessors(place).stream()
					.filter(transition -> transition.getSymbol().equals(symbol))
					.filter(marking::isTransitionEnabled)
					.forEach(activeTransitionsWithSymbol::add);
		}
		return activeTransitionsWithSymbol;
	}
	
	@Override
	public boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<C> stateFactory)
			throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Testing correctness of accepts");
		}

		final NestedWord<S> nw = NestedWord.nestedWord(mWord);
		final boolean resultAutomata =
				(new de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts<>(mServices,
						(new PetriNet2FiniteAutomaton<>(mServices, stateFactory, mOperand)).getResult(), nw))
								.getResult();
		final boolean correct = mResult == resultAutomata;

		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of accepts");
		}

		return correct;
	}
}
