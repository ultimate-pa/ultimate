/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.junit.Assert.assertNotNull;

import java.nio.file.Path;
import java.util.Set;
import java.util.stream.Stream;

import org.junit.runner.RunWith;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.EnumerateRuns;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.FactoryTestRunner;

@RunWith(FactoryTestRunner.class)
public class LiptonReductionRunAdaptationTests extends LiptonReductionTestsBase {
	private static final int RUN_LIMIT = 50;

	@Override
	protected void runTest(final Path path, final AutomataTestFileAST ast, final BoundedPetriNet<String, String> input,
			final BoundedPetriNet<String, String> expected,
			final IIndependenceRelation<Set<String>, String> independence) throws AutomataLibraryException {

		for (final var run : asIterable(EnumerateRuns.stream(input).limit(RUN_LIMIT))) {

			assert run.isRunOf(input) : "Failed to get a real run for the test: " + run;
			assert run.isAccepting(input) : "Failed to get an accepting run for the test: " + run;

			final var reduction = new LiptonReduction<>(mAutomataServices, input, CompositionFactory.INSTANCE,
					new CopyPlaceFactory(), independence, PostScriptChecker.INSTANCE, null, run);
			final BoundedPetriNet<String, String> actual = reduction.getResult();
			final var adaptedRun = reduction.getAdaptedRun();

			assertNotNull("Run could not ne adapted: " + run, adaptedRun);
			assertThat("Adapted run is not a real run: " + adaptedRun, adaptedRun.isRunOf(actual));
			assertThat("Adapted run is not accepting: " + adaptedRun, adaptedRun.isAccepting(actual));

			// TODO check covering: adapted run's word should cover original run's word
		}

	}

	private static <X> Iterable<X> asIterable(final Stream<X> stream) {
		return stream::iterator;
	}
}
