/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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
import java.util.Optional;
import java.util.stream.Stream;

import org.junit.runner.RunWith;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.EnumerateWords;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.AutomatonConstructingVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.DynamicPORVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.FactoryTestRunner;

@RunWith(FactoryTestRunner.class)
public class DynamicPORSoundnessTests extends DynamicPORTestsBase {

	@Override
	protected void runTest(final Path path, final AutomataTestFileAST ast,
			final NestedWordAutomaton<String, String> input, final NestedWordAutomaton<String, String> expected,
			final IIndependenceRelation<?, String> independence, final IDisabling<String> disabling,
			final IMembranes<String, String> membranes, final IEnabling<String, String> enabling)
			throws AutomataLibraryException {

		// check if every word of input is represented in expected result
		final var expectedCtex = findReductionCounterexample(expected, input, independence);
		assertThat("FLAWED TEST: Expected reduction " + expected + " is not a reduction of input " + input
				+ "counterexample: " + expectedCtex.orElse(null), expectedCtex.isEmpty());

		// check that expected reduction does not have new words
		final var expectedNew = findNewWord(input, expected);
		assertThat("FLAWED TEST: Expected reduction " + expected + " accepts a word not accepted by input " + input
				+ "word: " + expectedNew.orElse(null), expectedNew.isEmpty());

		// Perform DPOR
		final var constructor = new AutomatonConstructingVisitor<>(input, mAutomataServices, () -> "###empty###");
		final var dporvisitor = new DynamicPORVisitor<>(constructor, input, new AlphabeticOrder<>(), independence,
				disabling, membranes, enabling);
		DepthFirstTraversal.traverse(mAutomataServices, input, new AlphabeticOrder<>(), dporvisitor);
		final NestedWordAutomaton<String, String> actual = constructor.getReductionAutomaton();

		// check if every word of input is represented in expected result
		final var actualCtex = findReductionCounterexample(actual, input, independence);
		assertThat("Actual reduction " + actual + " is not a reduction of input " + input + "counterexample: "
				+ actualCtex.orElse(null), actualCtex.isEmpty());

		// check that actual reduction does not have new words
		final var actualNew = findNewWord(input, actual);
		assertThat("FLAWED TEST: Actual reduction " + actual + " accepts a word not accepted by input " + input
				+ "word: " + actualNew.orElse(null), actualNew.isEmpty());
	}

	private <S> Optional<Word<String>> findReductionCounterexample(final NestedWordAutomaton<String, S> reduction,
			final NestedWordAutomaton<String, S> original, final IIndependenceRelation<?, String> independence) {
		return EnumerateWords.stream(original).filter(w -> !hasRepresentative(reduction, w, independence)).findAny();
	}

	private <S> boolean hasRepresentative(final NestedWordAutomaton<String, S> reduction, final Word<String> w,
			final IIndependenceRelation<?, String> independence) {
		return generateEquivalenceClass(w, independence).anyMatch(v -> isAccepted(reduction, v));
	}

	private <S, L> Optional<Word<L>> findNewWord(final NestedWordAutomaton<L, S> input,
			final NestedWordAutomaton<L, S> reduction) {
		return EnumerateWords.stream(reduction).filter(w -> !isAccepted(input, w)).findAny();
	}

	private <L, S> boolean isAccepted(final NestedWordAutomaton<L, S> aut, final Word<L> word) {
		try {
			return new Accepts<>(mAutomataServices, aut, NestedWord.nestedWord(word), false, false).getResult();
		} catch (final AutomataLibraryException e) {
			throw new IllegalStateException("Failed to check acceptance", e);
		}
	}

	private static <L> Stream<Word<String>> generateEquivalenceClass(final Word<String> word,
			final IIndependenceRelation<?, String> independence) {
		return CoveringIterator.enumerateCoveringWords(word, independence, String.class);
	}
}
