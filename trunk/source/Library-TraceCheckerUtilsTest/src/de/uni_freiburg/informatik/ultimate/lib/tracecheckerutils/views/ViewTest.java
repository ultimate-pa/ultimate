package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views;

import java.util.List;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;

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
		final var incUpdates = IntStream.range(0, N).mapToObj(Integer::valueOf)
				.collect(Collectors.toMap(Function.identity(), i -> i + 1));
		final var decUpdates = IntStream.range(1, N + 1).mapToObj(Integer::valueOf)
				.collect(Collectors.toMap(Function.identity(), i -> i - 1));
		return new Program<>(null, List.of(new GlobalVarUpdate<>(incUpdates, IncDecLocation.MINUS, IncDecLocation.PLUS),
				new GlobalVarUpdate<>(decUpdates, IncDecLocation.PLUS, IncDecLocation.MINUS)));
	}

	public static Configuration<ProgramState<Integer, IncDecLocation>> mutexNInit(final int N) {
		final ProgramState<Integer, IncDecLocation> controller = new ProgramState.ControllerState<>(0);
		final ProgramState<Integer, IncDecLocation> thread = new ProgramState.ThreadState<>(IncDecLocation.MINUS);
		final var threads =
				new ImmutableList<>(IntStream.range(0, N).mapToObj(i -> thread).collect(Collectors.toList()));
		return new Configuration<>(new ImmutableList<>(controller, threads));
	}

	@Test
	public void exploreMutex2() {
		final var logger = UltimateMocks.createUltimateServiceProviderMock().getLoggingService().getLogger(getClass());
		new Explorer<>(mutexN(2), List.of(mutexNInit(2))).dfs(c -> logger.info(c));
	}

	@Test
	public void exploreMutex3() {
		final var logger = UltimateMocks.createUltimateServiceProviderMock().getLoggingService().getLogger(getClass());
		new Explorer<>(mutexN(3), List.of(mutexNInit(3))).dfs(c -> logger.info(c));
	}

	@Test
	public void exploreMutex4() {
		final var logger = UltimateMocks.createUltimateServiceProviderMock().getLoggingService().getLogger(getClass());
		new Explorer<>(mutexN(4), List.of(mutexNInit(4))).dfs(c -> logger.info(c));
	}
}
