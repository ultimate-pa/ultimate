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

import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.junit.runner.RunWith;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.EnumerateWords;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.LazyPetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.FactoryTestRunner;

@RunWith(FactoryTestRunner.class)
public class LiptonReductionSoundnessTests extends LiptonReductionTestsBase {
	private static final int WORD_LIMIT = 50;

	@Override
	protected void runTest(final Path path, final AutomataTestFileAST ast, final BoundedPetriNet<String, String> input,
			final BoundedPetriNet<String, String> expected,
			final IIndependenceRelation<Set<String>, String> independence) throws AutomataLibraryException {

		final var expectedCtex = findReductionCounterexample(expected, input, independence);
		assertThat("FLAWED TEST: Expected net " + expected + " is not a reduction of input " + input
				+ "counterexample: " + expectedCtex.orElse(null), expectedCtex.isEmpty());

		final var expectedNew = findNewWord(expected, input);
		assertThat("FLAWED TEST: Expected net " + expected + " contains words not accepted by input " + input
				+ "example: " + expectedNew.orElse(null), expectedNew.isEmpty());

		final var reduction = new LiptonReduction<>(mAutomataServices, input, CompositionFactory.INSTANCE,
				CopyPlaceFactory.INSTANCE, independence, PostScriptChecker.INSTANCE, null);
		reduction.performReduction();
		final BoundedPetriNet<String, String> actual = reduction.getResult();

		final var actualCtex = findReductionCounterexample(actual, input, independence);
		assertThat("Incorrect: Actual net " + actual + " is not a reduction of input " + input + "counterexample: "
				+ actualCtex.orElse(null), actualCtex.isEmpty());

		final var actualNew = findNewWord(actual, input);
		assertThat("Incorrect: Actual net " + actual + " contains words not accepted by input " + input + "example: "
				+ actualNew.orElse(null), actualNew.isEmpty());
	}

	private Optional<Word<String>> findReductionCounterexample(final IPetriNet<String, String> reduction,
			final IPetriNet<String, String> original, final IIndependenceRelation<Set<String>, String> independence)
			throws PetriNetNot1SafeException {
		final var originalAut =
				new LazyPetriNet2FiniteAutomaton<>(mAutomataServices, new StringPetriFactory(), original, null);
		return EnumerateWords.stream(originalAut, String.class).limit(WORD_LIMIT)
				.filter(w -> !hasRepresentative(reduction, w, independence)).findAny();
	}

	private Optional<Word<String>> findNewWord(final IPetriNet<String, String> reduction,
			final IPetriNet<String, String> original) throws AutomataLibraryException {
		final var reductionAut =
				new LazyPetriNet2FiniteAutomaton<>(mAutomataServices, new StringPetriFactory(), reduction, null);
		return EnumerateWords.stream(reductionAut, String.class).limit(WORD_LIMIT).filter(w -> !isAccepted(original, w))
				.findAny();
	}

	private boolean hasRepresentative(final IPetriNet<String, String> reduction, final Word<String> w,
			final IIndependenceRelation<Set<String>, String> independence) {
		return generateEquivalenceClass(w, independence).anyMatch(v -> isAccepted(reduction, v));
	}

	private boolean isAccepted(final IPetriNet<String, String> net, final Word<String> w) {
		final String flattenedW = flatten(w);
		try {
			return EnumerateWords
					.stream(new LazyPetriNet2FiniteAutomaton<>(mAutomataServices, new StringPetriFactory(), net, null),
							String.class)
					.takeWhile(v -> v.length() <= flattenedW.length()).anyMatch(v -> flatten(v).equals(flattenedW));
		} catch (final AutomataLibraryException e) {
			throw new RuntimeException(e);
		}
	}

	private static String flatten(final Word<String> word) {
		return word.asList().stream().collect(Collectors.joining());
	}

	private static Stream<Word<String>> generateEquivalenceClass(final Word<String> word,
			final IIndependenceRelation<?, String> independence) {
		return CoveringIterator.enumerateCoveringWords(word, independence, String.class);
	}

	private static class StringPetriFactory implements IPetriNet2FiniteAutomatonStateFactory<String> {
		private final Map<Marking<String>, String> mMap = new HashMap<>();

		@Override
		public String createEmptyStackState() {
			return "###emptystack###";
		}

		@Override
		public String getContentOnPetriNet2FiniteAutomaton(final Marking<String> marking) {
			return mMap.computeIfAbsent(marking, m -> m.stream().sorted().collect(Collectors.joining(";")));
		}
	}
}