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
import java.util.Set;

import org.junit.runner.RunWith;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.FactoryTestRunner;

@RunWith(FactoryTestRunner.class)
public class LiptonReductionTests extends LiptonReductionTestsBase {

	@Override
	protected void runTest(final Path path, final AutomataTestFileAST ast, final BoundedPetriNet<String, String> input,
			final BoundedPetriNet<String, String> expected,
			final IIndependenceRelation<Set<String>, String> independence) throws AutomataLibraryException {
		final var reduction = new LiptonReduction<>(mAutomataServices, input, CompositionFactory.INSTANCE,
				new CopyPlaceFactory(), independence, PostScriptChecker.INSTANCE, null);
		reduction.performReduction();
		final BoundedPetriNet<String, String> actual = reduction.getResult();

		assertThat("PNs differ, expected " + expected + " but actual was " + actual, areEqual(expected, actual));
	}

	private boolean areEqual(final BoundedPetriNet<String, String> first,
			final BoundedPetriNet<String, String> second) {
		if (!first.getAlphabet().equals(second.getAlphabet())) {
			mLogger.error("alphabet differs: %s != %s", first.getAlphabet(), second.getAlphabet());
			return false;
		}

		if (!first.getPlaces().equals(second.getPlaces())) {
			mLogger.error("places differ");
			return false;
		}

		if (!first.getInitialPlaces().equals(second.getInitialPlaces())) {
			mLogger.error("initial places differ");
			return false;
		}

		if (!first.getAcceptingPlaces().equals(second.getAcceptingPlaces())) {
			mLogger.error("accepting places differ");
			return false;
		}

		if (first.getTransitions().size() != second.getTransitions().size()) {
			mLogger.error("transition count differs");
			return false;
		}

		for (final var trans1 : first.getTransitions()) {
			boolean found = false;
			for (final var trans2 : second.getTransitions()) {
				if (!trans1.getSymbol().equals(trans2.getSymbol())) {
					continue;
				}
				if (!trans1.getPredecessors().equals(trans2.getPredecessors())) {
					continue;
				}
				if (!trans1.getSuccessors().equals(trans2.getSuccessors())) {
					continue;
				}
				found = true;
			}
			if (!found) {
				mLogger.error("no matching transition for " + trans1);
				return false;
			}
		}

		return true;
	}
}
