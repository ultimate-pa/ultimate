/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE ViewAbstractionTest Library.
 *
 * The ULTIMATE ViewAbstractionTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ViewAbstractionTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ViewAbstractionTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ViewAbstractionTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ViewAbstractionTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.test.systems;

import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Configuration;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Program;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.ProgramConfiguration;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.test.ViewTest;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.test.ViewTest.ITestProgram;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class German implements ITestProgram<ProgramConfiguration<Pair<Boolean, German.Comm>, German.LocalState>> {
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
	public Program<ProgramConfiguration<Pair<Boolean, German.Comm>, German.LocalState>> getTransitions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ProgramConfiguration<Pair<Boolean, Comm>, LocalState> init(final int parameter) {
		final var local = LocalState.initial();
		final var global = new Pair<>(false, Comm.eps);
		return new ProgramConfiguration<>(global,
				new Configuration<>(new ImmutableList<>(ViewTest.repeat(parameter, local))));
	}

	@Override
	public boolean isBad(final ProgramConfiguration<Pair<Boolean, Comm>, LocalState> config) {
		final var states = config.getThreadConfiguration().stream().map(s -> s.mState).collect(Collectors.toList());
		return states.stream().filter(Q.excl::equals).count() > 2
				|| (states.stream().anyMatch(Q.excl::equals) && states.stream().anyMatch(Q.shrd::equals));
	}
}