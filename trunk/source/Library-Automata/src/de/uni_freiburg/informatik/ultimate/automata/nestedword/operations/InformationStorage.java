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
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;

/**
 * Implementation of the Information Storage Operation for Partial Order Reduction.
 *
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            letter type
 * @param <S>
 *            state type
 */
public class InformationStorage<L, S> extends ProductNwa<L, S> {
	private final IIntersectionStateFactory<S> mStateFactory;

	/**
	 * Implementation of the Information Storage Operation for Partial Order Reduction.
	 *
	 * @param fstOperand
	 *            automaton in which the information shall be stored
	 * @param sndOperand
	 *            automaton from which the information shall be taken
	 * @param stateFactory
	 *            state factory 
	 * @param assumeInSndNonFinalIsTrap
	 *            assume that in the second operand a non-final state is a trap (i.e., whenever we reach a non-final
	 *            state we can never go back to a final state.
	 * @throws AutomataLibraryException
	 *             if alphabets differ                      
	 */
	public InformationStorage(INwaOutgoingLetterAndTransitionProvider<L, S> fstOperand,
			INwaOutgoingLetterAndTransitionProvider<L, S> sndOperand,
			final IIntersectionStateFactory<S> stateFactory, boolean assumeInSndNonFinalIsTrap) 
			throws AutomataLibraryException {
		super(fstOperand, sndOperand, stateFactory, assumeInSndNonFinalIsTrap);
		mStateFactory = stateFactory;
	}

	@Override
	protected final ProductNwa<L, S>.ProductState createProductState(S fst, S snd) {
		final S res = mStateFactory.intersection(fst, snd);
		final boolean isAccepting = mFstOperand.isFinal(fst);
		return new ProductState(fst, snd, res, isAccepting);
	}
}
