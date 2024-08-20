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

import java.util.ArrayList;
import java.util.function.UnaryOperator;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.BroadcastRule;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.Configuration;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.IRule;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.Program;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.ViewTest.ITestProgram;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.systems.Mutex.IncDecLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class MutexBroadcast implements ITestProgram<Pair<IncDecLocation, Integer>> {
	private final int mBound;

	public MutexBroadcast(final int bound) {
		mBound = bound;
	}

	@Override
	public Program<Pair<IncDecLocation, Integer>> getTransitions() {
		final var rules = new ArrayList<IRule<Pair<IncDecLocation, Integer>>>();

		final UnaryOperator<Pair<IncDecLocation, Integer>> incBroadcast =
				st -> new Pair<>(st.getFirst(), st.getSecond() + 1);
		for (int i = 0; i < mBound; ++i) {
			rules.add(new BroadcastRule<>(new Pair<>(IncDecLocation.MINUS, i), new Pair<>(IncDecLocation.PLUS, i + 1),
					incBroadcast));
		}

		final UnaryOperator<Pair<IncDecLocation, Integer>> decBroadcast =
				st -> new Pair<>(st.getFirst(), st.getSecond() - 1);
		for (int i = 0; i <= mBound; ++i) {
			// implicitly puts a guard on the decrement
			rules.add(new BroadcastRule<>(new Pair<>(IncDecLocation.PLUS, i), new Pair<>(IncDecLocation.MINUS, i - 1),
					decBroadcast));
		}

		return new Program<>(null, rules);
	}

	@Override
	public Configuration<Pair<IncDecLocation, Integer>> init(final int parameter) {
		final var state = new Pair<>(IncDecLocation.MINUS, 0);
		final var states =
				new ImmutableList<>(IntStream.range(0, parameter).mapToObj(i -> state).collect(Collectors.toList()));
		return new Configuration<>(states);
	}

	@Override
	public boolean isBad(final Configuration<Pair<IncDecLocation, Integer>> config) {
		return config.stream().anyMatch(s -> s.getFirst() == IncDecLocation.PLUS && s.getSecond() == 0);
	}

}