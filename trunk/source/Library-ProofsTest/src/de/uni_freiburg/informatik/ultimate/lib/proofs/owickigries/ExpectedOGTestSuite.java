/*
 * Copyright (C) 2025 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2025 University of Freiburg
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

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.junit.runner.RunWith;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtParserUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.proofs.ThreadModularPrePostSpecification;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.FactoryTestRunner;

@RunWith(FactoryTestRunner.class)
public class ExpectedOGTestSuite extends OwickiGriesTestSuite {

	@Override
	protected void runTest(final Path path, final AutomataTestFileAST ast,
			final BoundedPetriNet<SimpleAction, IPredicate> program,
			final IPetriNetSuccessorProvider<SimpleAction, IPredicate> refinedPetriNet,
			final BranchingProcess<SimpleAction, IPredicate> unfolding,
			final IPossibleInterferences<Transition<SimpleAction, IPredicate>, IPredicate> possibleInterferences)
			throws AutomataLibraryException, IOException {
		final var unifier = mUnifiers.get(0);

		final var spec =
				new ThreadModularPrePostSpecification<>(Map.of(Marking.initial(program), unifier.getTruePredicate()),
						program::isAccepting, unifier.getFalsePredicate());
		final var annotation = new OwickiGriesParser<SimpleAction, IPredicate>(mProgramPlaceMap::get,
				(ghosts, str) -> parsePredicate(ghosts, str, unifier)).parse(program, mSymbolTable,
						Set.of(SimpleAction.PROCEDURE), spec, possibleInterferences, computeOGPath(path));

		assert new PetriOwickiGriesValidityCheck<>(mServices, mMgdScript, mHtc, program, annotation)
				.isValid() != Validity.INVALID : "Specified annotation is invalid";
	}

	@Override
	protected boolean includeTest(final Path path) {
		return Files.exists(computeOGPath(path));
	}

	private static Path computeOGPath(final Path atsPath) {
		final String filename = atsPath.getFileName().toString();
		final String basename = filename.substring(0, filename.lastIndexOf('.'));
		return atsPath.resolveSibling(basename + ".og.yml");
	}

	protected IPredicate parsePredicate(final Set<IProgramVar> ghostVariables, final String state,
			final IPredicateUnifier unifier) {
		final Set<TermVariable> termVars = Stream.concat(ghostVariables.stream(), mSymbolTable.getGlobals().stream())
				.map(IProgramVar::getTermVariable).collect(Collectors.toSet());
		final Term term = SmtParserUtils.parseWithVariables(state, mServices, mMgdScript, termVars);

		// TODO unifier does not know ghost variables!
		return unifier.getOrConstructPredicate(term);
	}

}
