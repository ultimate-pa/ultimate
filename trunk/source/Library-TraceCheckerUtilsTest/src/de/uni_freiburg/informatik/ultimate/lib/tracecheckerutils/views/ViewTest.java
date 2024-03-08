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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.UnaryOperator;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.GlobalRule.Quantifier;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.GlobalRule.Range;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class ViewTest {
	enum IncDecLocation {
		MINUS("⊖"), PLUS("⨁");

		private final String mStr;

		private IncDecLocation(final String str) {
			mStr = str;
		}

		@Override
		public String toString() {
			return mStr;
		}
	}

	public static Program<ProgramState<Integer, IncDecLocation>> mutexN(final int N) {
		return new Program<>(null,
				List.of(new GlobalVarUpdate<>(IncDecLocation.MINUS, IncDecLocation.PLUS, i -> i < N ? i + 1 : null),
						new GlobalVarUpdate<>(IncDecLocation.PLUS, IncDecLocation.MINUS, i -> i - 1)));
	}

	public static Configuration<ProgramState<Integer, IncDecLocation>> mutexNInit(final int N) {
		final ProgramState<Integer, IncDecLocation> controller = new ProgramState.ControllerState<>(0);
		final ProgramState<Integer, IncDecLocation> thread = new ProgramState.ThreadState<>(IncDecLocation.MINUS);
		final var threads =
				new ImmutableList<>(IntStream.range(0, N).mapToObj(i -> thread).collect(Collectors.toList()));
		return new Configuration<>(new ImmutableList<>(controller, threads));
	}

	private void exploreMutex(final int N) {
		final var logger = UltimateMocks.createUltimateServiceProviderMock().getLoggingService().getLogger(getClass());
		new Explorer<>(mutexN(N), List.of(mutexNInit(N))).dfs(logger::info);
	}

	@Test
	public void exploreMutex2() {
		exploreMutex(2);
	}

	@Test
	public void exploreMutex3() {
		exploreMutex(3);
	}

	@Test
	public void exploreMutex4() {
		exploreMutex(4);
	}

	public static Program<Pair<IncDecLocation, Integer>> mutexNBroadcast(final int N) {
		final var rules = new ArrayList<IRule<Pair<IncDecLocation, Integer>>>();

		final UnaryOperator<Pair<IncDecLocation, Integer>> incBroadcast =
				st -> new Pair<>(st.getFirst(), st.getSecond() + 1);
		for (int i = 0; i < N; ++i) {
			rules.add(new BroadcastRule<>(new Pair<>(IncDecLocation.MINUS, i), new Pair<>(IncDecLocation.PLUS, i + 1),
					incBroadcast));
		}

		final UnaryOperator<Pair<IncDecLocation, Integer>> decBroadcast =
				st -> new Pair<>(st.getFirst(), st.getSecond() - 1);
		for (int i = 0; i <= N; ++i) {
			// implicitly puts a guard on the decrement
			rules.add(new BroadcastRule<>(new Pair<>(IncDecLocation.PLUS, i), new Pair<>(IncDecLocation.MINUS, i - 1),
					decBroadcast));
		}

		return new Program<>(null, rules);
	}

	public static Configuration<Pair<IncDecLocation, Integer>> mutexNBroadcastInit(final int N) {
		final var state = new Pair<>(IncDecLocation.MINUS, 0);
		final var states = new ImmutableList<>(IntStream.range(0, N).mapToObj(i -> state).collect(Collectors.toList()));
		return new Configuration<>(states);
	}

	private void exploreMutexBroadcast(final int N) {
		final var logger = UltimateMocks.createUltimateServiceProviderMock().getLoggingService().getLogger(getClass());
		new Explorer<>(mutexNBroadcast(N), List.of(mutexNBroadcastInit(N))).dfs(logger::info);
	}

	@Test
	public void exploreMutex2Broadcast() {
		exploreMutexBroadcast(2);
	}

	@Test
	public void exploreMutex3Broadcast() {
		exploreMutexBroadcast(3);
	}

	@Test
	public void exploreMutex4Broadcast() {
		exploreMutexBroadcast(4);
	}

	public enum Burns {
		q1, q2, q3, q4, q5, q6, q7;
	}

	public static Program<Pair<Burns, Boolean>> burns() {
		final List<IRule<Pair<Burns, Boolean>>> rules = Arrays.asList(
				// first rule
				new LocalRule<>(new Pair<>(Burns.q1, true), new Pair<>(Burns.q2, false)),
				new LocalRule<>(new Pair<>(Burns.q1, false), new Pair<>(Burns.q2, false)),

				// second rule
				new GlobalRule<>(new Pair<>(Burns.q2, true), new Pair<>(Burns.q2, true), Range.LESS, Quantifier.EXISTS,
						Pair::getSecond),
				new GlobalRule<>(new Pair<>(Burns.q2, false), new Pair<>(Burns.q2, false), Range.LESS,
						Quantifier.EXISTS, Pair::getSecond),

				// third rule
				new GlobalRule<>(new Pair<>(Burns.q2, true), new Pair<>(Burns.q3, true), Range.LESS, Quantifier.FORALL,
						s -> !s.getSecond()),
				new GlobalRule<>(new Pair<>(Burns.q2, false), new Pair<>(Burns.q3, false), Range.LESS,
						Quantifier.FORALL, s -> !s.getSecond()),

				// fourth rule
				new LocalRule<>(new Pair<>(Burns.q3, true), new Pair<>(Burns.q4, true)),
				new LocalRule<>(new Pair<>(Burns.q3, false), new Pair<>(Burns.q4, true)),

				// fifth rule
				new GlobalRule<>(new Pair<>(Burns.q3, true), new Pair<>(Burns.q4, true), Range.LESS, Quantifier.EXISTS,
						Pair::getSecond),
				new GlobalRule<>(new Pair<>(Burns.q3, false), new Pair<>(Burns.q4, false), Range.LESS,
						Quantifier.EXISTS, Pair::getSecond),

				// sixth rule
				new GlobalRule<>(new Pair<>(Burns.q4, true), new Pair<>(Burns.q5, true), Range.LESS, Quantifier.FORALL,
						s -> !s.getSecond()),
				new GlobalRule<>(new Pair<>(Burns.q4, false), new Pair<>(Burns.q5, false), Range.LESS,
						Quantifier.FORALL, s -> !s.getSecond()),

				// seventh rule
				new GlobalRule<>(new Pair<>(Burns.q5, true), new Pair<>(Burns.q6, true), Range.GREATER,
						Quantifier.FORALL, s -> !s.getSecond()),
				new GlobalRule<>(new Pair<>(Burns.q5, false), new Pair<>(Burns.q6, false), Range.GREATER,
						Quantifier.FORALL, s -> !s.getSecond()),

				// eigth rule
				new LocalRule<>(new Pair<>(Burns.q6, true), new Pair<>(Burns.q7, false)),
				new LocalRule<>(new Pair<>(Burns.q6, false), new Pair<>(Burns.q7, false)),

				// ninth rule
				new LocalRule<>(new Pair<>(Burns.q7, true), new Pair<>(Burns.q1, true)),
				new LocalRule<>(new Pair<>(Burns.q7, false), new Pair<>(Burns.q1, false))

		);

		return new Program<>(null, rules);
	}

	public static Configuration<Pair<Burns, Boolean>> burnsInit(final int n) {
		final var state = new Pair<>(Burns.q1, false);
		final var states = new ImmutableList<>(IntStream.range(0, n).mapToObj(i -> state).collect(Collectors.toList()));
		return new Configuration<>(states);
	}

	private void exploreBurns(final int n) {
		final var logger = UltimateMocks.createUltimateServiceProviderMock().getLoggingService().getLogger(getClass());
		new Explorer<>(burns(), List.of(burnsInit(n))).dfs(logger::info);
	}

	@Test
	public void exploreBurns2() {
		exploreBurns(2);
	}

	@Test
	public void exploreBurns3() {
		exploreBurns(3);
	}

	@Test
	public void exploreBurns4() {
		exploreBurns(4);
	}
}
