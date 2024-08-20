/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtilsTest Library.
 *
 * The ULTIMATE TraceCheckerUtilsTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtilsTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtilsTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtilsTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtilsTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.systems;

import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.Configuration;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.Program;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.ProgramState;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.ViewTest;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.ViewTest.ITestProgram;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class German implements ITestProgram<ProgramState<Pair<Boolean, German.Comm>, German.LocalState>> {
	enum Comm {
		eps, reqShr, reqExc
	}

	enum Q {
		invl, shrd, excl
	}

	enum CH1 {
		eps, reqShr, reqExc
	}

	enum CH2 {
		eps, graShr, graExc, invldt
	}

	enum CH3 {
		eps, invAck
	}

	public static class LocalState {
		private final German.Q mState;
		private final German.CH1 mCh1;
		private final German.CH2 mCh2;
		private final German.CH3 mCh3;
		private final boolean mCurClt;
		private final boolean mSList;
		private final boolean mIList;

		public LocalState(final German.Q state, final German.CH1 ch1, final German.CH2 ch2, final German.CH3 ch3,
				final boolean curClt, final boolean sList, final boolean iList) {
			mState = state;
			mCh1 = ch1;
			mCh2 = ch2;
			mCh3 = ch3;
			mCurClt = curClt;
			mSList = sList;
			mIList = iList;
		}

		public static German.LocalState initial() {
			return new LocalState(Q.invl, CH1.eps, CH2.eps, CH3.eps, false, false, false);
		}
	}

	@Override
	public Program<ProgramState<Pair<Boolean, German.Comm>, German.LocalState>> getTransitions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Configuration<ProgramState<Pair<Boolean, German.Comm>, German.LocalState>> init(final int parameter) {
		final ProgramState<Pair<Boolean, German.Comm>, German.LocalState> local =
				new ProgramState.ThreadState<>(LocalState.initial());
		final ProgramState<Pair<Boolean, German.Comm>, German.LocalState> global =
				new ProgramState.ControllerState<>(new Pair<>(false, Comm.eps));
		return new Configuration<>(new ImmutableList<>(global, ViewTest.repeat(parameter, local)));
	}

	@Override
	public boolean isBad(final Configuration<ProgramState<Pair<Boolean, German.Comm>, German.LocalState>> config) {
		final var states = config.stream().filter(ProgramState::isThreadState).map(s -> s.getThreadState().mState)
				.collect(Collectors.toList());
		return states.stream().filter(Q.excl::equals).count() > 2
				|| (states.stream().anyMatch(Q.excl::equals) && states.stream().anyMatch(Q.shrd::equals));
	}
}