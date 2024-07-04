package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries;

import java.io.IOException;
import java.nio.file.Path;
import java.util.Set;
import java.util.function.Function;

import org.junit.runner.RunWith;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.PetriHistoryOwickiGries;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.PetriOwickiGries;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.FactoryTestRunner;

@RunWith(FactoryTestRunner.class)
public class PetriHistoryOwickiGriesTestSuite extends OwickiGriesTestSuite {
	@Override
	protected void runTest(final Path path, final AutomataTestFileAST ast,
			final BoundedPetriNet<SimpleAction, IPredicate> program,
			final BoundedPetriNet<SimpleAction, IPredicate> refinedPetriNet,
			final BranchingProcess<SimpleAction, IPredicate> unfolding) throws AutomataLibraryException, IOException {
		final var construction = new PetriHistoryOwickiGries<>(mServices, unfolding, program, Function.identity(),
				mMgdScript, mSymbolTable, Set.of(SimpleAction.PROCEDURE), mTotalizedProofs);

		final var annotation = construction.getResult();
		mLogger.info(
				"Computed Owicki-Gries annotation with %d ghost variables, %d ghost updates, and overall size %d\n%s",
				annotation.getGhostVariables().size(), annotation.getAssignmentMapping().size(), annotation.size(),
				annotation);

		// check validity of annotation
		assert new OwickiGriesValidityCheck<>(mServices, mMgdScript, mHtc, annotation,
				PetriOwickiGries.getCoMarkedPlaces(unfolding))
						.isValid() != Validity.INVALID : "Invalid Owicki-Gries annotation";
	}
}
