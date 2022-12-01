/*
 * Copyright (C) 2011-2015 Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2022 University of Freiburg
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

import java.util.ArrayDeque;
import java.util.ArrayList;
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
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Acceptance test for Petri nets.
 *
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            symbol type
 * @param <PLACE>
 *            place content type
 */
public final class Accepts<LETTER, PLACE>
		extends UnaryNetOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {
	private final IPetriNetTransitionProvider<LETTER, PLACE> mOperand;
	private final Word<LETTER> mWord;

	private final PetriNetRun<LETTER, PLACE> mAcceptingRun;

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

		mAcceptingRun = dfs();

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
		return mAcceptingRun != null;
	}

	public PetriNetRun<LETTER, PLACE> getAcceptingRun() {
		return mAcceptingRun;
	}

	private PetriNetRun<LETTER, PLACE> dfs() throws AutomataOperationCanceledException {
		final var initialMarking = new Marking<>(ImmutableSet.of(mOperand.getInitialPlaces()));
		if (mWord.length() == 0) {
			if (mOperand.isAccepting(initialMarking)) {
				return new PetriNetRun<>(initialMarking);
			}
			return null;
		}

		final var worklist = new ArrayDeque<DfsRecord<LETTER, PLACE>>();
		worklist.push(new DfsRecord<>(initialMarking));

		while (!worklist.isEmpty()) {
			if (isCancellationRequested()) {
				throw new AutomataOperationCanceledException(getClass());
			}

			final var current = worklist.pop();

			final LETTER symbol = mWord.getSymbol(current.mPosition);
			if (!mOperand.getAlphabet().contains(symbol)) {
				throw new IllegalArgumentException("Symbol " + symbol + " not in alphabet");
			}

			for (final var transition : activeTransitionsWithSymbol(current.getMarking(), symbol)) {
				final var next = new DfsRecord<>(current, transition);
				if (next.mPosition >= mWord.length() && mOperand.isAccepting(next.getMarking())) {
					return buildRun(next);
				}
				if (next.mPosition < mWord.length()) {
					worklist.push(next);
				}
			}
		}

		return null;
	}

	private PetriNetRun<LETTER, PLACE> buildRun(final DfsRecord<LETTER, PLACE> dfsRecord) {
		final var markings = new ArrayList<Marking<PLACE>>();
		final var transitions = new ArrayList<Transition<LETTER, PLACE>>();
		for (int i = 0; i < dfsRecord.mTransitionStack.size(); ++i) {
			markings.add(0, dfsRecord.mMarkingStack.get(i));
			transitions.add(0, dfsRecord.mTransitionStack.get(i));
		}
		markings.add(0, dfsRecord.mMarkingStack.get(dfsRecord.mMarkingStack.size() - 1));
		return new PetriNetRun<>(markings, mWord, transitions);
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
		final boolean correct = getResult() == resultAutomata;

		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of accepts");
		}

		return correct;
	}

	private static class DfsRecord<L, P> {
		private final ImmutableList<Marking<P>> mMarkingStack;
		private final ImmutableList<Transition<L, P>> mTransitionStack;
		private final int mPosition;

		public DfsRecord(final Marking<P> initial) {
			mMarkingStack = ImmutableList.singleton(initial);
			mTransitionStack = ImmutableList.empty();
			mPosition = 0;
		}

		public DfsRecord(final DfsRecord<L, P> parent, final Transition<L, P> nextTransition) {
			assert parent.getMarking().isTransitionEnabled(nextTransition);
			Marking<P> marking;
			try {
				marking = parent.getMarking().fireTransition(nextTransition);
			} catch (final PetriNetNot1SafeException e) {
				throw new AssertionError(e);
			}

			mMarkingStack = new ImmutableList<>(marking, parent.mMarkingStack);
			mTransitionStack = new ImmutableList<>(nextTransition, parent.mTransitionStack);
			mPosition = parent.mPosition + 1;
		}

		Marking<P> getMarking() {
			return mMarkingStack.getHead();
		}
	}
}
