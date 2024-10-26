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
package de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.test;

import java.util.List;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.Explorer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.ViewAbstractionComputation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.ViewAbstractionComputation.Status;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Configuration;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Program;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.test.systems.BurnsRezine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.test.systems.BurnsSimple;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.test.systems.Firefly;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.test.systems.Illinois;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.test.systems.Mutex;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.test.systems.MutexBroadcast;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;

public class ViewTest {
	private static final int MAX_ITERATIONS = 100;

	private static <X> Consumer<Configuration<X>> consumeConfiguration(final IUltimateServiceProvider services,
			final Predicate<Configuration<X>> isBad) {
		final var logger = services.getLoggingService().getLogger(ViewTest.class);
		return config -> {
			logger.info(config);
			if (isBad != null && isBad.test(config)) {
				logger.fatal("bad config: %s", config);
				throw new BadConfigurationException(config);
			}
		};
	}

	private static <X> void explore(final ITestProgram<X> program, final int parameter) {
		final var services = UltimateMocks.createUltimateServiceProviderMock();
		new Explorer<>(program.getTransitions(), List.of(program.init(parameter)))
				.dfs(consumeConfiguration(services, program::isBad));
	}

	private static <X> void abstractFp(final ITestProgram<X> program, final int parameter) {
		abstractFp(program, parameter, -1);
	}

	private static <X> void abstractFp(final ITestProgram<X> program, final int parameter, final int maxIterations) {
		final var services = UltimateMocks.createUltimateServiceProviderMock();
		final var va = new ViewAbstractionComputation<>(services, program.getTransitions(),
				Set.of(program.init(parameter)), parameter);
		final var status = va.run(maxIterations);
		final var fp = va.getCurrentAbstraction();

		final var logger = services.getLoggingService().getLogger(ViewTest.class);
		if (status == Status.COMPLETED) {
			logger.info("Fixpoint computation completed after %d iterations", va.getCurrentIteration());
		} else {
			logger.info("Fixpoint computation aborted");
		}
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

	@Test(expected = BadConfigurationException.class)
	public void abstract2Mutex2() {
		abstractFp(new Mutex(2), 2, MAX_ITERATIONS);
	}

	@Test
	public void abstract3Mutex2() {
		abstractFp(new Mutex(2), 3);
	}

	@Test(expected = BadConfigurationException.class)
	public void abstract3Mutex3() {
		abstractFp(new Mutex(3), 3, MAX_ITERATIONS);
	}

	@Test
	public void abstract4Mutex3() {
		abstractFp(new Mutex(3), 4);
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

	@Test(expected = BadConfigurationException.class)
	public void abstract2MutexBroadcast2() {
		abstractFp(new MutexBroadcast(2), 2, MAX_ITERATIONS);
	}

	@Test
	public void abstract3MutexBroadcast2() {
		abstractFp(new MutexBroadcast(2), 3);
	}

	@Test(expected = BadConfigurationException.class)
	public void abstract3MutexBroadcast3() {
		abstractFp(new MutexBroadcast(3), 3, MAX_ITERATIONS);
	}

	@Test
	public void abstract4MutexBroadcast3() {
		abstractFp(new MutexBroadcast(3), 4);
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

	@Test
	public void exploreIllinois2() {
		explore(new Illinois(), 2);
	}

	@Test
	public void exploreIllinois3() {
		explore(new Illinois(), 3);
	}

	@Test
	public void exploreIllinois4() {
		explore(new Illinois(), 4);
	}

	@Test
	public void abstractIllinois2() {
		abstractFp(new Illinois(), 2);
	}

	@Test
	public void abstractIllinois3() {
		abstractFp(new Illinois(), 3);
	}

	@Test
	public void exploreFirefly2() {
		explore(new Firefly(), 2);
	}

	@Test
	public void exploreFirefly3() {
		explore(new Firefly(), 3);
	}

	@Test
	public void exploreFirefly4() {
		explore(new Firefly(), 4);
	}

	@Test
	public void abstractFirefly2() {
		abstractFp(new Firefly(), 2);
	}

	@Test
	public void abstractFirefly3() {
		abstractFp(new Firefly(), 3);
	}

	public static <X> ImmutableList<X> repeat(final int n, final X elem) {
		return new ImmutableList<>(IntStream.range(0, n).mapToObj(i -> elem).collect(Collectors.toList()));
	}

	public interface ITestProgram<X> {
		Program<X> getTransitions();

		Configuration<X> init(int parameter);

		boolean isBad(Configuration<X> config);
	}

	public static class BadConfigurationException extends RuntimeException {
		private final Configuration<?> mBadConfig;

		public BadConfigurationException(final Configuration<?> badConfig) {
			super("Bad configuration: " + badConfig);
			mBadConfig = badConfig;
		}
	}
}
