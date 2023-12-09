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
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import org.junit.runner.RunWith;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.FactoryTestRunner;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

@RunWith(FactoryTestRunner.class)
public class NaiveOwickiGriesTestSuite extends OwickiGriesTestSuite {
	@Override
	protected void runTest(final Path path, final AutomataTestFileAST ast,
			final BoundedPetriNet<SimpleAction, IPredicate> program,
			final BoundedPetriNet<SimpleAction, IPredicate> refinedPetriNet,
			final BranchingProcess<SimpleAction, IPredicate> unfolding) throws AutomataLibraryException {
		mLogger.info("Constructing Owicki-Gries proof for Petri program that %s and unfolding that %s",
				program.sizeInformation(), unfolding.sizeInformation());

		// construct Floyd-Hoare annotation
		final var floydHoare = new PetriFloydHoare<>(mServices, mMgdScript, mSymbolTable, unfolding,
				Function.identity(), program, mUnifiers, true, true);
		final Map<Marking<IPredicate>, IPredicate> petriFloydHoare = floydHoare.getResult();
		mLogger.info("Computed Floyd-Hoare proof with %d non-trivial markings and assertion size %d",
				petriFloydHoare.size(), computeFloydHoareSize(petriFloydHoare));

		// check validity of Floyd-Hoare annotation
		assert checkFloydHoareValidity(program, petriFloydHoare) : "Invalid Floyd-Hoare annotation";

		// construct Owicki-Gries annotation
		final var construction = new OwickiGriesConstruction<>(mServices, mMgdScript, mSymbolTable,
				Set.of(SimpleAction.PROCEDURE), program, petriFloydHoare, true);
		final var annotation = construction.getResult();
		mLogger.info("Computed Owicki-Gries annotation with %d ghost variables, %d ghost updates, and overall size %d",
				annotation.getGhostVariables().size(), annotation.getAssignmentMapping().size(), annotation.size());

		// check validity of annotation
		assert new OwickiGriesValidityCheck<>(mServices, mMgdScript, mHtc, annotation, construction.getCoMarkedPlaces())
				.isValid() != Validity.INVALID : "Invalid Owicki-Gries annotation";
	}

	private boolean checkFloydHoareValidity(final BoundedPetriNet<SimpleAction, IPredicate> program,
			final Map<Marking<IPredicate>, IPredicate> petriFloydHoare) throws PetriNetNot1SafeException {
		final HashRelation<String, IProgramNonOldVar> rel = new HashRelation<>();
		rel.addAllPairs(SimpleAction.PROCEDURE, mSymbolTable.getGlobals());
		final var modGlob = new ModifiableGlobalsTable(rel);
		return new PetriFloydHoareValidityCheck<>(mServices, mMgdScript, mSymbolTable, modGlob, program,
				petriFloydHoare).isValid() != Validity.INVALID;
	}

	private static long computeFloydHoareSize(final Map<Marking<IPredicate>, IPredicate> petriFloydHoare) {
		final DAGSize sizeComputation = new DAGSize();
		return petriFloydHoare.entrySet().stream()
				.collect(Collectors.summingLong(x -> sizeComputation.size(x.getValue().getFormula())));
	}
}
