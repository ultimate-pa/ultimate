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
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.GlobalRule.Quantifier;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.GlobalRule.Range;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.ViewTest.BurnsRezine.Burns;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.ViewTest.BurnsSimple.B;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.ViewTest.Mutex.IncDecLocation;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class ViewTest {
	public static class Mutex implements ITestProgram<ProgramState<Integer, IncDecLocation>> {
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

		private final int mBound;

		public Mutex(final int bound) {
			mBound = bound;
		}

		@Override
		public Program<ProgramState<Integer, IncDecLocation>> getTransitions() {
			return new Program<>(null,
					List.of(new GlobalVarUpdate<>(IncDecLocation.MINUS, IncDecLocation.PLUS,
							i -> (mBound == -1 || i < mBound) ? i + 1 : null),
							new GlobalVarUpdate<>(IncDecLocation.PLUS, IncDecLocation.MINUS, i -> i - 1)));
		}

		@Override
		public Configuration<ProgramState<Integer, IncDecLocation>> init(final int parameter) {
			final ProgramState<Integer, IncDecLocation> controller = new ProgramState.ControllerState<>(0);
			final ProgramState<Integer, IncDecLocation> thread = new ProgramState.ThreadState<>(IncDecLocation.MINUS);
			final var threads = new ImmutableList<>(
					IntStream.range(0, parameter).mapToObj(i -> thread).collect(Collectors.toList()));
			return new Configuration<>(new ImmutableList<>(controller, threads));
		}

		@Override
		public boolean isBad(final Configuration<ProgramState<Integer, IncDecLocation>> config) {
			return config.stream().anyMatch(s -> s.isThreadState() && s.getThreadState() == IncDecLocation.PLUS)
					&& config.stream().filter(s -> s.isControllerState()).findAny().get().getControllerState() == 0;
		}

	}

	private static <X> Consumer<Configuration<X>> consumeConfiguration(final IUltimateServiceProvider services,
			final Predicate<Configuration<X>> isBad) {
		final var logger = services.getLoggingService().getLogger(ViewTest.class);
		return config -> {
			logger.info(config);
			if (isBad != null && isBad.test(config)) {
				logger.fatal("bad config: %s", config);
				throw new AssertionError("bad config: " + config);
			}
		};
	}

	private static <X> void explore(final ITestProgram<X> program, final int parameter) {
		final var services = UltimateMocks.createUltimateServiceProviderMock();
		new Explorer<>(program.getTransitions(), List.of(program.init(parameter)))
				.dfs(consumeConfiguration(services, program::isBad));
	}

	private static <X> void abstractFp(final ITestProgram<X> program, final int parameter) {
		final var services = UltimateMocks.createUltimateServiceProviderMock();
		final var va = new ViewAbstraction<>(services, program.getTransitions());
		final var fp = va.computeFixedPoint(Set.of(program.init(parameter)), parameter);

		final var logger = services.getLoggingService().getLogger(ViewTest.class);
		fp.stream().forEach(consumeConfiguration(services, program::isBad));
		logger.info(fp);
	}

	@Test
	public void exploreMutex2() {
		explore(new Mutex(2), 2);
	}

	@Test
	public void exploreMutex3() {
		explore(new Mutex(3), 3);
	}

	@Test
	public void exploreMutex4() {
		explore(new Mutex(4), 4);
	}

	@Test
	public void abstract3Mutex2() {
		abstractFp(new Mutex(2), 3);
	}

	@Test
	public void abstract4Mutex3() {
		abstractFp(new Mutex(3), 4);
	}

	public static class MutexBroadcast implements ITestProgram<Pair<IncDecLocation, Integer>> {
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
				rules.add(new BroadcastRule<>(new Pair<>(IncDecLocation.MINUS, i),
						new Pair<>(IncDecLocation.PLUS, i + 1), incBroadcast));
			}

			final UnaryOperator<Pair<IncDecLocation, Integer>> decBroadcast =
					st -> new Pair<>(st.getFirst(), st.getSecond() - 1);
			for (int i = 0; i <= mBound; ++i) {
				// implicitly puts a guard on the decrement
				rules.add(new BroadcastRule<>(new Pair<>(IncDecLocation.PLUS, i),
						new Pair<>(IncDecLocation.MINUS, i - 1), decBroadcast));
			}

			return new Program<>(null, rules);
		}

		@Override
		public Configuration<Pair<IncDecLocation, Integer>> init(final int parameter) {
			final var state = new Pair<>(IncDecLocation.MINUS, 0);
			final var states = new ImmutableList<>(
					IntStream.range(0, parameter).mapToObj(i -> state).collect(Collectors.toList()));
			return new Configuration<>(states);
		}

		@Override
		public boolean isBad(final Configuration<Pair<IncDecLocation, Integer>> config) {
			return config.stream().anyMatch(s -> s.getFirst() == IncDecLocation.PLUS && s.getSecond() == 0);
		}

	}

	@Test
	public void exploreMutex2Broadcast() {
		explore(new MutexBroadcast(2), 2);
	}

	@Test
	public void exploreMutex3Broadcast() {
		explore(new MutexBroadcast(3), 3);
	}

	@Test
	public void exploreMutex4Broadcast() {
		explore(new MutexBroadcast(4), 4);
	}

	@Test
	public void abstract3MutexBroadcast2() {
		abstractFp(new MutexBroadcast(2), 3);
	}

	@Test
	public void abstract4MutexBroadcast3() {
		abstractFp(new MutexBroadcast(3), 4);
	}

	// version of Burns protocol as in Ahmed Rezine's PhD thesis
	public static class BurnsRezine implements ITestProgram<Pair<Burns, Boolean>> {
		public enum Burns {
			q1, q2, q3, q4, q5, q6, q7;
		}

		@Override
		public Program<Pair<Burns, Boolean>> getTransitions() {
			final List<IRule<Pair<Burns, Boolean>>> rules = Arrays.asList(
					// first rule
					new LocalRule<>(new Pair<>(Burns.q1, true), new Pair<>(Burns.q2, false)),
					new LocalRule<>(new Pair<>(Burns.q1, false), new Pair<>(Burns.q2, false)),

					// second rule
					new GlobalRule<>(new Pair<>(Burns.q2, true), new Pair<>(Burns.q2, true), Range.LESS,
							Quantifier.EXISTS, Pair::getSecond),
					new GlobalRule<>(new Pair<>(Burns.q2, false), new Pair<>(Burns.q2, false), Range.LESS,
							Quantifier.EXISTS, Pair::getSecond),

					// third rule
					new GlobalRule<>(new Pair<>(Burns.q2, true), new Pair<>(Burns.q3, true), Range.LESS,
							Quantifier.FORALL, s -> !s.getSecond()),
					new GlobalRule<>(new Pair<>(Burns.q2, false), new Pair<>(Burns.q3, false), Range.LESS,
							Quantifier.FORALL, s -> !s.getSecond()),

					// fourth rule
					new LocalRule<>(new Pair<>(Burns.q3, true), new Pair<>(Burns.q4, true)),
					new LocalRule<>(new Pair<>(Burns.q3, false), new Pair<>(Burns.q4, true)),

					// fifth rule
					new GlobalRule<>(new Pair<>(Burns.q3, true), new Pair<>(Burns.q4, true), Range.LESS,
							Quantifier.EXISTS, Pair::getSecond),
					new GlobalRule<>(new Pair<>(Burns.q3, false), new Pair<>(Burns.q4, false), Range.LESS,
							Quantifier.EXISTS, Pair::getSecond),

					// sixth rule
					new GlobalRule<>(new Pair<>(Burns.q4, true), new Pair<>(Burns.q5, true), Range.LESS,
							Quantifier.FORALL, s -> !s.getSecond()),
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

		@Override
		public Configuration<Pair<Burns, Boolean>> init(final int parameter) {
			final var state = new Pair<>(Burns.q1, false);
			final var states = new ImmutableList<>(
					IntStream.range(0, parameter).mapToObj(i -> state).collect(Collectors.toList()));
			return new Configuration<>(states);
		}

		@Override
		public boolean isBad(final Configuration<Pair<Burns, Boolean>> config) {
			return config.stream().filter(s -> s.getFirst() == Burns.q6).limit(2).count() > 1;
		}
	}

	@Test
	public void exploreBurnsRezine2() {
		explore(new BurnsRezine(), 2);
	}

	@Test
	public void exploreBurnsRezine3() {
		explore(new BurnsRezine(), 3);
	}

	@Test
	public void exploreBurnsRezine4() {
		explore(new BurnsRezine(), 4);
	}

	@Test
	public void abstractBurnsRezine2() {
		abstractFp(new BurnsRezine(), 2);
	}

	@Test
	public void abstractBurnsRezine3() {
		abstractFp(new BurnsRezine(), 3);
	}

	public static class BurnsSimple implements ITestProgram<B> {
		public enum B {
			green, white, black, yellow, blue, red
		}

		@Override
		public Program<B> getTransitions() {
			final Predicate<B> ybr = Set.of(B.yellow, B.blue, B.red)::contains;
			final Predicate<B> gwb = Set.of(B.green, B.white, B.black)::contains;
			return new Program<>(null,
					List.of(new LocalRule<>(B.green, B.white),
							new GlobalRule<>(B.white, B.green, Range.LESS, Quantifier.EXISTS, ybr),
							new GlobalRule<>(B.white, B.black, Range.LESS, Quantifier.FORALL, gwb),
							new LocalRule<>(B.black, B.yellow),
							new GlobalRule<>(B.yellow, B.green, Range.LESS, Quantifier.EXISTS, ybr),
							new GlobalRule<>(B.yellow, B.blue, Range.LESS, Quantifier.FORALL, gwb),
							new GlobalRule<>(B.blue, B.red, Range.GREATER, Quantifier.FORALL, gwb),
							new LocalRule<>(B.red, B.green)));
		}

		@Override
		public Configuration<B> init(final int parameter) {
			return new Configuration<>(new ImmutableList<>(
					IntStream.range(0, parameter).mapToObj(i -> B.green).collect(Collectors.toList())));
		}

		@Override
		public boolean isBad(final Configuration<B> config) {
			return config.stream().filter(s -> s == B.red).limit(2).count() > 1;
		}

	}

	@Test
	public void exploreBurnsSimple2() {
		explore(new BurnsSimple(), 2);
	}

	@Test
	public void exploreBurnsSimple3() {
		explore(new BurnsSimple(), 3);
	}

	@Test
	public void exploreBurnsSimple4() {
		explore(new BurnsSimple(), 4);
	}

	@Test
	public void abstractBurnsSimple2() {
		abstractFp(new BurnsSimple(), 2);
	}

	@Test
	public void abstractBurnsSimple3() {
		abstractFp(new BurnsSimple(), 3);
	}

	public interface ITestProgram<X> {
		Program<X> getTransitions();

		Configuration<X> init(int parameter);

		boolean isBad(Configuration<X> config);
	}
}
