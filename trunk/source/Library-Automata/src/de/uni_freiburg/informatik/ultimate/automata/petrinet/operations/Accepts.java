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
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Acceptance test for Petri nets.
 *
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            symbol type
 * @param <PLACE>
 *            place content type
 */
public final class Accepts<LETTER, PLACE>
		extends UnaryNetOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {
	private final IPetriNetTransitionProvider<LETTER, PLACE> mOperand;
	private final Word<LETTER> mWord;
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
	 * @throws PetriNetNot1SafeException
	 */
	public Accepts(final AutomataLibraryServices services, final IPetriNetTransitionProvider<LETTER, PLACE> operand,
			final Word<LETTER> word) throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services);
		mOperand = operand;
		mWord = word;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		mResult = getResultHelper(0, new Marking<>(ImmutableSet.of(operand.getInitialPlaces())));

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	@Override
	public String startMessage() {
		return "Start " + getOperationName() + ". Operand " + mOperand.sizeInformation();
	}

	@Override
	protected IPetriNetTransitionProvider<LETTER, PLACE> getOperand() {
		return mOperand;
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}

	private boolean getResultHelper(final int position, final Marking<PLACE> marking)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		if (position >= mWord.length()) {
			return mOperand.isAccepting(marking);
		}

		if (isCancellationRequested()) {
			throw new AutomataOperationCanceledException(this.getClass());
		}

		final LETTER symbol = mWord.getSymbol(position);
		if (!mOperand.getAlphabet().contains(symbol)) {
			throw new IllegalArgumentException("Symbol " + symbol + " not in alphabet");
		}

		final int nextPosition = position + 1;
		boolean result = false;
		Marking<PLACE> nextMarking;
		for (final Transition<LETTER, PLACE> transition : activeTransitionsWithSymbol(marking, symbol)) {
			nextMarking = marking.fireTransition(transition);
			if (getResultHelper(nextPosition, nextMarking)) {
				result = true;
			}
		}
		return result;
	}

	private Set<Transition<LETTER, PLACE>> activeTransitionsWithSymbol(final Marking<PLACE> marking,
			final LETTER symbol) {
		final Set<Transition<LETTER, PLACE>> activeTransitionsWithSymbol = new HashSet<>();
		for (final PLACE place : marking) {
			mOperand.getSuccessors(place).stream().filter(transition -> transition.getSymbol().equals(symbol))
					.filter(marking::isTransitionEnabled).forEach(activeTransitionsWithSymbol::add);
		}
		return activeTransitionsWithSymbol;
	}

	@Override
	public boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<PLACE> stateFactory)
			throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Testing correctness of accepts");
		}

		final NestedWord<LETTER> nw = NestedWord.nestedWord(mWord);
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
