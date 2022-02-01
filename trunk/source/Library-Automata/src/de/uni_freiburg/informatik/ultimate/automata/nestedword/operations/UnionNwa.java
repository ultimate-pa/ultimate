/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IUnionStateFactory;

/**
 * On-the-fly union of two nested word automata.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
class UnionNwa<LETTER, STATE> extends ProductNwa<LETTER, STATE> {
	private final IUnionStateFactory<STATE> mStateFactory;

	/**
	 * @param fstOperand
	 *            First operand.
	 * @param sndOperand
	 *            second operand
	 * @param stateFactory
	 *            state factory
	 * @param assumeInSndNonFinalIsTrap
	 *            assume that in the second operand a non-final state is a trap (i.e., whenever we reach a non-final
	 *            state we can never go back to a final state. 2016-11-19 Matthias: I don't know if "trap" is well-known
	 *            terminology or a term that we invented.)
	 * @throws AutomataLibraryException
	 *             if alphabets differ
	 */
	public UnionNwa(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOperand,
			final IUnionStateFactory<STATE> stateFactory, final boolean assumeInSndNonFinalIsTrap)
			throws AutomataLibraryException {
		super(fstOperand, sndOperand, stateFactory, assumeInSndNonFinalIsTrap);
		mStateFactory = stateFactory;
	}

	@Override
	protected final ProductState createProductState(final STATE fst, final STATE snd) {
		final STATE res = mStateFactory.union(fst, snd);
		final boolean isAccepting = mFstOperand.isFinal(fst) || mSndOperand.isFinal(snd);
		return new ProductState(fst, snd, res, isAccepting);
	}
}
