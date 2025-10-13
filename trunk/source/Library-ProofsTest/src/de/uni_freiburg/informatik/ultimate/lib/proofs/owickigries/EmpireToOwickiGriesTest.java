/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE ProofsTest Library.
 *
 * The ULTIMATE ProofsTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ProofsTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ProofsTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ProofsTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ProofsTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries;

import static org.hamcrest.CoreMatchers.equalTo;
import static org.junit.Assert.assertEquals;
import static org.junit.Assume.assumeThat;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import org.junit.runner.RunWith;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireToOwickiGries;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireValidityCheck;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.Region;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.Territory;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.FactoryTestRunner;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

@RunWith(FactoryTestRunner.class)
public class EmpireToOwickiGriesTest extends OwickiGriesTestSuite {
	@Override
	protected void runTest(final Path path, final AutomataTestFileAST ast,
			final BoundedPetriNet<SimpleAction, IPredicate> program,
			final IPetriNetSuccessorProvider<SimpleAction, IPredicate> refinedPetriNet,
			final BranchingProcess<SimpleAction, IPredicate> unfolding,
			final IPossibleInterferences<Transition<SimpleAction, IPredicate>, IPredicate> possibleInterferences)
			throws AutomataLibraryException, IOException {

		final var unifier = mUnifiers.get(0);
		final var implicationChecker = new MonolithicImplicationChecker(mServices, mMgdScript);
		final var modifiableGlobals = computeModifiableGlobals();

		final var empire = new EmpireAnnotationParser<>(mProgramPlaceMap::get, s -> parsePredicate(s, unifier),
				unifier::getOrConstructPredicateForConjunction).parse(computeEmpirePath(path));
		mLogger.info("Parsed Empire annotation:\n%s", empire);

		final var assertionPlaces = mProofs.stream().map(
				(Function<? super NestedWordAutomaton<SimpleAction, IPredicate>, ? extends Set<IPredicate>>) NestedWordAutomaton::getStates)
				.flatMap(Set::stream).collect(Collectors.toSet());
		final var predicatePlaceMap = new HashMap<IPredicate, Set<IPredicate>>();
		for (final Pair<Territory<IPredicate, Region<IPredicate>>, IPredicate> pair : empire.getEmpire()) {
			final var law = pair.getSecond();
			for (final IPredicate iPredicate : assertionPlaces) {
				if (law.getFormula().equals(iPredicate.getFormula())) {
					predicatePlaceMap.put(law, Set.of(iPredicate));
				}
			}
		}
		final var empireCheck = new EmpireValidityCheck<>(mServices, mMgdScript, implicationChecker, mPredicateFactory,
				program, modifiableGlobals, empire);
		assumeThat("Given empire annotation is not valid", empireCheck.getValidity(), equalTo(Validity.VALID));

		final var empireToOwickiGries = new EmpireToOwickiGries<>(mServices, mMgdScript, program, mSymbolTable,
				Set.of(SimpleAction.PROCEDURE), empire, possibleInterferences);

		final var owickiGries = empireToOwickiGries.getAnnotation();
		mLogger.info("Computed Owicki-Gries annotation:\n%s", owickiGries);
		mLogger.info("Owicki-Gries annotation size: %s", owickiGries.size());

		final var owickiGriesCheck =
				new PetriOwickiGriesValidityCheck<>(mServices, mMgdScript, program, modifiableGlobals, owickiGries);
		assertEquals("Computed Owicki-Gries annotation is not valid.", Validity.VALID, owickiGriesCheck.isValid());
	}

	@Override
	protected boolean includeTest(final Path path) {
		return Files.exists(computeEmpirePath(path));
	}

	private static Path computeEmpirePath(final Path atsPath) {
		final String filename = atsPath.getFileName().toString();
		final String basename = filename.substring(0, filename.lastIndexOf('.'));
		return atsPath.resolveSibling(basename + ".empire.yml");
	}
}
