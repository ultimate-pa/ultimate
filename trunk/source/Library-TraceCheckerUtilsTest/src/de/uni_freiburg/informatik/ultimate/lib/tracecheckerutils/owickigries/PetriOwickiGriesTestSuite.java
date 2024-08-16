/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries;

import java.nio.file.Path;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import org.junit.runner.RunWith;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.TotalizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.UnionNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.PetriOwickiGries;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.FactoryTestRunner;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

@RunWith(FactoryTestRunner.class)
public class PetriOwickiGriesTestSuite extends OwickiGriesTestSuite {
	@Override
	protected void runTest(final Path path, final AutomataTestFileAST ast,
			final BoundedPetriNet<SimpleAction, IPredicate> program,
			final BoundedPetriNet<SimpleAction, IPredicate> refinedPetriNet,
			final BranchingProcess<SimpleAction, IPredicate> unfolding) throws AutomataLibraryException {
		// Assume.assumeTrue("More than one proof", mUnifiers.size() == 1);
		final var proofPlaces = mProofs.stream().map(nwa -> nwa.getStates()).collect(Collectors.toList());
		final var factory = new PredicateFactoryForInterpolantAutomata(mMgdScript,
				new PredicateFactory(mServices, mMgdScript, mSymbolTable), true);
		INwaOutgoingLetterAndTransitionProvider<SimpleAction, IPredicate> product = mProofs.get(0);
		for (var i = 1; i < mProofs.size(); i++) {
			final var proof = mProofs.get(i);
			final var initialTrueState1 = DataStructureUtils.getOneAndOnly(product.getInitialStates(), "initial state");
			final var totalizedProduct = new TotalizeNwa<>(product, initialTrueState1, false);
			final var initialTrueState2 = DataStructureUtils.getOneAndOnly(proof.getInitialStates(), "initial state");
			final var totalizedProof = new TotalizeNwa<>(proof, initialTrueState2, false);
			final var u = new UnionNwa<>(totalizedProduct, totalizedProof, factory, false);
			product = u;
		}
		product = new NestedWordAutomatonReachableStates<>(mAutomataServices, product);
		final StatisticsData data = new StatisticsData();
		final var pog = new PetriOwickiGries<>(mServices, unfolding, program, mPredicateFactory, Function.identity(),
				mMgdScript, mSymbolTable, Set.of(SimpleAction.PROCEDURE), computeModifiableGlobals(), proofPlaces,
				product);
		data.aggregateBenchmarkData(pog.getStatistics());
		mLogger.info("PetriOwickiGries Statistics: %s", data);
	}
}
