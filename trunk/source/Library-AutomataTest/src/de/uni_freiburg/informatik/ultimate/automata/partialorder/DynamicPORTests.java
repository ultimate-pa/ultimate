/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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
import java.util.Comparator;

import org.junit.runner.RunWith;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.AutomatonConstructingVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.DynamicPORVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.ReachabilityCheckVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.FactoryTestRunner;

@RunWith(FactoryTestRunner.class)
public class DynamicPORTests extends DynamicPORTestsBase {

	@Override
	protected void runTest(final Path path, final AutomataTestFileAST ast,
			final NestedWordAutomaton<String, String> input, final NestedWordAutomaton<String, String> expected,
			final IIndependenceRelation<?, String> independence) throws AutomataLibraryException {
		final var constructor = new AutomatonConstructingVisitor<>(input, mAutomataServices, () -> "###empty###");

		// TODO wrap constructor in DynamicPORVisitor, or otherwise modify the code to apply DPOR.
		final IDfsVisitor<String, String> visitor = constructor;
		final var dporvisitor = new DynamicPORVisitor<>(visitor, input, new AlphabeticOrder<>());

		DepthFirstTraversal.traverse(mAutomataServices, input, new AlphabeticOrder<>(), dporvisitor);
		final NestedWordAutomaton<String, String> actual = constructor.getReductionAutomaton();

		assertThat("Automata differ, expected " + expected + " but actual was " + actual, areEqual(expected, actual));
	}

	private boolean areEqual(final NestedWordAutomaton<String, String> first,
			final NestedWordAutomaton<String, String> second) {
		if ((first == null) != (second == null)) {
			mLogger.error("only one automata is null");
			return false;
		}

		assert NestedWordAutomataUtils.isFiniteAutomaton(first);
		assert NestedWordAutomataUtils.isFiniteAutomaton(second);

		if (!first.getAlphabet().equals(second.getAlphabet())) {
			mLogger.error("alphabet differs: %s != %s", first.getAlphabet(), second.getAlphabet());
			return false;
		}

		if (!first.getStates().equals(second.getStates())) {
			mLogger.error("states differ");
			return false;
		}

		if (!first.getInitialStates().equals(second.getInitialStates())) {
			mLogger.error("initial states differ");
			return false;
		}

		if (!first.getFinalStates().equals(second.getFinalStates())) {
			mLogger.error("accepting states differ");
			return false;
		}

		for (final var state : first.getStates()) {
			if (!first.lettersInternal(state).equals(second.lettersInternal(state))) {
				mLogger.error("outgoing letters for state %s differ", state);
				return false;
			}

			for (final var letter : first.lettersInternal(state)) {
				if (!first.succInternal(state, letter).equals(second.succInternal(state, letter))) {
					mLogger.error("successors for state %s under letter %s differ", state, letter);
					return false;
				}
			}
		}

		return true;
	}

	private class AlphabeticOrder<S> implements IDfsOrder<String, S> {
		@Override
		public Comparator<String> getOrder(final S state) {
			return Comparator.naturalOrder();
		}

		@Override
		public boolean isPositional() {
			return false;
		}
	}
}
