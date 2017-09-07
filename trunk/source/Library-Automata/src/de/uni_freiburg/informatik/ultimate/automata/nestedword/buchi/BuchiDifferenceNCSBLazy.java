/*
 * Copyright (C) 2017 Yong Li (liyong@ios.ac.cn)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NwaOutgoingLetterAndTransitionAdapter;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiComplementNcsbStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;

/**
 * Buchi difference "<tt>NCSBLazy</tt>".
 * 
 * @author Yong Li (liyong@ios.ac.cn)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class BuchiDifferenceNCSBLazy<LETTER, STATE> extends AbstractBuchiDifference<LETTER, STATE> {


	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param fstOperand
	 *            first operand
	 * @param sndOperand
	 *            second operand
	 * @throws AutomataLibraryException
	 *             if construction fails
	 */
	public <SF extends IBuchiComplementNcsbStateFactory<STATE> & IBuchiIntersectStateFactory<STATE> & IEmptyStackStateFactory<STATE>> BuchiDifferenceNCSBLazy(
			final AutomataLibraryServices services, final SF stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOperand) throws AutomataLibraryException {
		super(services, fstOperand, sndOperand);

		if (!NestedWordAutomataUtils.isFiniteAutomaton(sndOperand)) {
			throw new UnsupportedOperationException("Calls and returns are not yet supported.");
		}
		
		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}
		constructResult(stateFactory);
		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	private <SF extends IBuchiComplementNcsbStateFactory<STATE> & IBuchiIntersectStateFactory<STATE> & IEmptyStackStateFactory<STATE>>
			void constructResult(final SF stateFactory) throws AutomataLibraryException {
		final BuchiComplementNCSBLazyNwa<LETTER, STATE> onDemandComplemented = new BuchiComplementNCSBLazyNwa<>(mServices, stateFactory, mSndOperand);
		mSndComplemented = new NwaOutgoingLetterAndTransitionAdapter<LETTER, STATE>(onDemandComplemented);
		constructDifferenceFromComplement(stateFactory);
	}

}
