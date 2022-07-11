/*
 * Copyright (C) 2020 Marcel Ebbinghaus
 * Copyright (C) 2020 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMonitorStateFactory;

/**
 * A product automaton construction in which the second operand acts only as a monitor: It never blocks, and acceptance
 * is purely determined by the first operand.
 *
 * @author Marcel Ebbinghaus
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            letter type
 * @param <S>
 *            state type
 */
public class MonitorProduct<L, S> extends ProductNwa<L, S, S, S> {
	private final IMonitorStateFactory<S, S, S> mStateFactory;

	/**
	 * Implementation of the Information Storage Operation for Partial Order Reduction.
	 *
	 * @param fstOperand
	 *            automaton in which the information shall be stored
	 * @param sndOperand
	 *            automaton from which the information shall be taken
	 * @param stateFactory
	 *            state factory
	 * @throws AutomataLibraryException
	 *             if alphabets differ
	 */
	public MonitorProduct(final INwaOutgoingLetterAndTransitionProvider<L, S> fstOperand,
			final INwaOutgoingLetterAndTransitionProvider<L, S> sndOperand,
			final IMonitorStateFactory<S, S, S> stateFactory) throws AutomataLibraryException {
		super(fstOperand, sndOperand, stateFactory, false);
		mStateFactory = stateFactory;
	}

	@Override
	protected final ProductNwa<L, S, S, S>.ProductState createProductState(final S fst, final S snd) {
		final S res = mStateFactory.product(fst, snd);
		final boolean isAccepting = mFstOperand.isFinal(fst);
		return new ProductState(fst, snd, res, isAccepting);
	}
}
