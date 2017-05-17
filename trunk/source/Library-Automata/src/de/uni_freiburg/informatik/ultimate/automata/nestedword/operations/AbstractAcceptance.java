/*
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Contains methods which are shared by {@link Accepts} and
 * {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiAccepts BuchiAccepts}.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public abstract class AbstractAcceptance<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {
	private static final String AT_POSITION = " at position ";
	private static final String UNABLE_TO_CHECK_ACCEPTANCE_LETTER = "Unable to check acceptance. Letter ";

	protected final INestedWordAutomatonSimple<LETTER, STATE> mOperand;

	protected boolean mIsAccepted;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 */
	public AbstractAcceptance(final AutomataLibraryServices services,
			final INestedWordAutomatonSimple<LETTER, STATE> operand) {
		super(services);
		mOperand = operand;
	}

	/**
	 * @param states
	 *            states
	 * @return Result contains a configuration for each state which contains only this state.
	 */
	public Set<ArrayDeque<STATE>> emptyStackConfiguration(final Iterable<STATE> states) {
		final Set<ArrayDeque<STATE>> configurations = new HashSet<>();
		for (final STATE state : states) {
			final ArrayDeque<STATE> singletonStack = new ArrayDeque<>();
			singletonStack.push(state);
			configurations.add(singletonStack);
		}
		return configurations;
	}

	/**
	 * @return true iff the topmost stack element is an accepting state.
	 */
	protected boolean isAcceptingConfiguration(final Deque<STATE> configuration,
			final INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		final STATE state = configuration.peek();
		return nwa.isFinal(state);
	}

	/**
	 * Compute successor configurations for a set of given configurations and one letter of a nested word. A
	 * configuration is given as a stack of states. (topmost element: current state, other elements: states occurred on
	 * a run at call positions) If the letter is at an internal position we consider only internal successors. If the
	 * letter is at a call position we consider only call successors. If the letter is at a return position we consider
	 * only return successors and consider the second topmost stack element as hierarchical predecessor.
	 * 
	 * @param position
	 *            of the symbol in the nested word for which the successors are computed.
	 * @param addInitial
	 *            if true we add for each initial state an stack that contains only this initial state. Useful to check
	 *            if suffix of word is accepted. If set the input configurations is modified.
	 * @throws AutomataLibraryException
	 *             if symbol not contained in alphabet or timeout
	 */
	protected Set<ArrayDeque<STATE>> successorConfigurations(final Set<ArrayDeque<STATE>> configurations,
			final NestedWord<LETTER> nestedWord, final int position,
			final INestedWordAutomatonSimple<LETTER, STATE> nwa, final boolean addInitial)
			throws AutomataLibraryException {
		final Set<ArrayDeque<STATE>> succConfigs = new HashSet<>();
		if (addInitial) {
			/**
			 * TODO Christian 2016-08-16: Most probably a bug: Does not make sense.
			 */
			configurations.addAll(configurations);
		}
		for (final ArrayDeque<STATE> config : configurations) {
			if (isCancellationRequested()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}

			final STATE state = config.pop();
			final LETTER symbol = nestedWord.getSymbol(position);
			if (nestedWord.isInternalPosition(position)) {
				successorConfigurationsInternal(position, nwa, succConfigs, config, state, symbol);
			} else if (nestedWord.isCallPosition(position)) {
				successorConfigurationsCall(position, nwa, succConfigs, config, state, symbol);
			} else if (nestedWord.isReturnPosition(position)) {
				successorConfigurationsReturn(position, nwa, succConfigs, config, state, symbol);
			} else {
				throw new AssertionError();
			}
			config.push(state);
		}
		return succConfigs;
	}

	private void successorConfigurationsInternal(final int position,
			final INestedWordAutomatonSimple<LETTER, STATE> nwa, final Set<ArrayDeque<STATE>> succConfigs,
			final ArrayDeque<STATE> config, final STATE state, final LETTER symbol) throws AutomataLibraryException {
		if (!nwa.getVpAlphabet().getInternalAlphabet().contains(symbol)) {
			throw new AutomataLibraryException(this.getClass(), UNABLE_TO_CHECK_ACCEPTANCE_LETTER + symbol + AT_POSITION
					+ position + " not in internal alphabet of automaton.");
		}
		final Iterable<OutgoingInternalTransition<LETTER, STATE>> outTransitions =
				nwa.internalSuccessors(state, symbol);
		for (final OutgoingInternalTransition<LETTER, STATE> outRans : outTransitions) {
			final STATE succ = outRans.getSucc();
			final ArrayDeque<STATE> succConfig = config.clone();
			succConfig.push(succ);
			succConfigs.add(succConfig);
		}
	}

	private void successorConfigurationsCall(final int position, final INestedWordAutomatonSimple<LETTER, STATE> nwa,
			final Set<ArrayDeque<STATE>> succConfigs, final ArrayDeque<STATE> config, final STATE state,
			final LETTER symbol) throws AutomataLibraryException {
		if (!nwa.getVpAlphabet().getCallAlphabet().contains(symbol)) {
			throw new AutomataLibraryException(this.getClass(), UNABLE_TO_CHECK_ACCEPTANCE_LETTER + symbol + AT_POSITION
					+ position + " not in call alphabet of automaton.");
		}
		final Iterable<OutgoingCallTransition<LETTER, STATE>> outTransitions = nwa.callSuccessors(state, symbol);
		for (final OutgoingCallTransition<LETTER, STATE> outRans : outTransitions) {
			final STATE succ = outRans.getSucc();
			final ArrayDeque<STATE> succConfig = config.clone();
			succConfig.push(state);
			succConfig.push(succ);
			succConfigs.add(succConfig);
		}
	}

	private void successorConfigurationsReturn(final int position, final INestedWordAutomatonSimple<LETTER, STATE> nwa,
			final Set<ArrayDeque<STATE>> succConfigs, final ArrayDeque<STATE> config, final STATE state,
			final LETTER symbol) throws AutomataLibraryException {
		if (!nwa.getVpAlphabet().getReturnAlphabet().contains(symbol)) {
			throw new AutomataLibraryException(this.getClass(), UNABLE_TO_CHECK_ACCEPTANCE_LETTER + symbol + AT_POSITION
					+ position + " not in return alphabet of automaton.");
		}
		if (config.isEmpty()) {
			if (mLogger.isWarnEnabled()) {
				mLogger.warn("Input has pending returns, we reject such words");
			}
		} else {
			final STATE callPred = config.pop();
			final Iterable<OutgoingReturnTransition<LETTER, STATE>> outTransitions =
					nwa.returnSuccessors(state, callPred, symbol);
			for (final OutgoingReturnTransition<LETTER, STATE> outRans : outTransitions) {
				final STATE succ = outRans.getSucc();
				final ArrayDeque<STATE> succConfig = config.clone();
				succConfig.push(succ);
				succConfigs.add(succConfig);
			}
			config.push(callPred);
		}
	}

	@Override
	protected INestedWordAutomatonSimple<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public Boolean getResult() {
		return mIsAccepted;
	}
}
