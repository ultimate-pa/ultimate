/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.AbstractIntersect;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Buchi intersect with double deckers.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class BuchiIntersectDD<LETTER, STATE> extends AbstractIntersect<LETTER, STATE> {
	private final IBuchiIntersectStateFactory<STATE> mStateFactory;

	/**
	 * Constructor which does not minimize the result.
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
	public BuchiIntersectDD(final AutomataLibraryServices services,
			final IBuchiIntersectStateFactory<STATE> stateFactory,
			final INestedWordAutomatonSimple<LETTER, STATE> fstOperand,
			final INestedWordAutomatonSimple<LETTER, STATE> sndOperand) throws AutomataLibraryException {
		this(services, stateFactory, fstOperand, sndOperand, false);
	}

	/**
	 * Full constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param fstNwa
	 *            first operand
	 * @param sndNwa
	 *            second operand
	 * @param minimizeResult
	 *            {@code true} iff result is minimized
	 * @throws AutomataLibraryException
	 *             if construction fails
	 */
	public BuchiIntersectDD(final AutomataLibraryServices services,
			final IBuchiIntersectStateFactory<STATE> stateFactory,
			final INestedWordAutomatonSimple<LETTER, STATE> fstNwa,
			final INestedWordAutomatonSimple<LETTER, STATE> sndNwa, final boolean minimizeResult)
			throws AutomataLibraryException {
		super(services, stateFactory, fstNwa, sndNwa, minimizeResult);
		mStateFactory = stateFactory;

		run();

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	@Override
	public String operationName() {
		return "BuchiIntersectDD";
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		if (mLogger.isWarnEnabled()) {
			mLogger.warn("No result check for " + operationName() + " available yet.");
		}
		return true;
	}

	@Override
	protected STATE intersect(final STATE fst, final STATE snd, final int track) {
		return mStateFactory.intersectBuchi(fst, snd, track);
	}

	@Override
	protected int getSuccTrack(final int stateTrack, final STATE fstState, final STATE sndState) {
		if (stateTrack == 1) {
			if (mFstNwa.isFinal(fstState)) {
				return 2;
			}
			return 1;
		}
		assert stateTrack == 2;
		if (mSndNwa.isFinal(sndState)) {
			return 1;
		}
		return 2;
	}

	@Override
	protected boolean isFinal(final STATE fst, final STATE snd) {
		return mFstNwa.isFinal(fst);
	}
}
