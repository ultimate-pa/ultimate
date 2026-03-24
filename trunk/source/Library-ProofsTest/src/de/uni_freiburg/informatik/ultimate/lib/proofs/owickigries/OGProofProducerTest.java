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

import java.io.IOException;
import java.nio.file.Path;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.function.Function;

import org.junit.runner.RunWith;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.EmpireAutomataOwickiGries.FocusComputation;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.OwickiGriesSettings.OwickiGriesComputation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.FactoryTestRunner;
import de.uni_freiburg.informatik.ultimate.util.VMUtils;
import de.uni_freiburg.informatik.ultimate.util.statistics.TimeTracker;

@RunWith(FactoryTestRunner.class)
public abstract class OGProofProducerTest extends OwickiGriesTestSuite {
	// Proof printing is disabled for benchmarking purposes, as in particular the naive construction often yields proofs
	// that exceed the maximum supported string length, and printing them leads to OOMs.
	// Also, it leads to gigantic log files.
	private static final boolean PRINT_FULL_PROOF = false;

	// Set this Java system property to 'true' in order to validate Owicki-Gries annotations after computation
	// (adding -DOwickiGries.Validate=true to the command line, or using the JAVA_TOOL_OPTIONS environment variable).
	// Annotations are always validated if asserts are enabled (-ea), so this only has an effect if asserts are off.
	private static final String PROPERTY_VALIDATE_OG = "OwickiGries.Validate";

	@Override
	protected void runTest(final Path path, final AutomataTestFileAST ast,
			final BoundedPetriNet<SimpleAction, IPredicate> program,
			final IPetriNetSuccessorProvider<SimpleAction, IPredicate> refinedPetriNet,
			final BranchingProcess<SimpleAction, IPredicate> unfolding,
			final IPossibleInterferences<Transition<SimpleAction, IPredicate>, IPredicate> possibleInterferences)
			throws AutomataLibraryException, IOException {
		mLogger.info("Constructing Owicki-Gries proof for Petri program that %s.", program.sizeInformation());

		final var overallTimeTracker = new TimeTracker();
		overallTimeTracker.start();

		final var producer = createProofProducer(program);

		// feed the required information to the producer (simulate the CEGAR loop)
		producer.initialize(possibleInterferences);
		for (int i = 0; i < mProofs.size(); ++i) {
			producer.refine(mUnifiers.get(i), mProofs.get(i), mBacktranslations.get(i));
		}
		producer.finalize(refinedPetriNet, unfolding);

		// let producer compute the proof
		assert producer.isReadyToComputeProof();
		final var annotation = producer.getOrComputeProof();

		overallTimeTracker.stop();
		mLogger.info("Complete Proof Computation Time: %dms", overallTimeTracker.elapsedTime(TimeUnit.MILLISECONDS));

		validateAnnotation(program, annotation);

		mLogger.info("Computed Owicki-Gries annotation with %d ghost variables, %d ghost updates, and overall size %d",
				annotation.getGhostVariables().size(), annotation.getAssignmentMapping().size(), annotation.size());
		if (PRINT_FULL_PROOF) {
			mLogger.info(annotation);
		}

		// print proof producer statistics
		mLogger.info(producer.getStatistics());

		// TODO temporary; integrate this into the regular statistics
		OwickiGriesStatistics.printModularityData(mLogger, annotation);
	}

	protected CfgSmtToolkit createCsToolkit() {
		return new CfgSmtToolkit(computeModifiableGlobals(), mMgdScript, mSymbolTable, Set.of(SimpleAction.PROCEDURE),
				Map.of(), Map.of(), null, null, null);
	}

	protected abstract IPetriNetProofProducer<SimpleAction, IPredicate>
			createProofProducer(final IPetriNet<SimpleAction, IPredicate> program);

	protected abstract OwickiGriesSettings getSettings();

	private void validateAnnotation(final BoundedPetriNet<SimpleAction, IPredicate> program,
			final OwickiGriesAnnotation<Transition<SimpleAction, IPredicate>, IPredicate, Marking<IPredicate>> annotation) {
		assert annotation != null;
		if (!validationEnabled()) {
			return;
		}

		mLogger.info("Checking validity of Owicki-Gries annotation...");
		final var validationTimeTracker = new TimeTracker();
		validationTimeTracker.start();

		try {
			final var check = new PetriOwickiGriesValidityCheck<>(mServices, mMgdScript, program,
					computeModifiableGlobals(), annotation);
			switch (check.isValid()) {
			case INVALID -> throw new AssertionError("Owicki-Gries annotation is invalid.");
			case UNKNOWN -> mLogger.warn("Validity check said UNKNOWN");
			case VALID -> mLogger.info("Validity check succeeded.");
			case NOT_CHECKED -> throw new IllegalStateException("Validity check said NOT_CHECKED");
			}
		} finally {
			validationTimeTracker.stop();
			mLogger.info("Owicki-Gries Validation Time: %dms",
					validationTimeTracker.elapsedTime(TimeUnit.MILLISECONDS));
		}
	}

	private static boolean validationEnabled() {
		if (VMUtils.areAssertionsEnabled()) {
			// if assertions are enabled, the producers already carry out a validity check
			return false;
		}

		final String validation = System.getProperty(PROPERTY_VALIDATE_OG, "false");
		assert validation != null;
		return Boolean.parseBoolean(validation);
	}

	public static final class NaiveOG extends OGProofProducerTest {
		@Override
		protected IPetriNetProofProducer<SimpleAction, IPredicate>
				createProofProducer(final IPetriNet<SimpleAction, IPredicate> program) {
			return new NaiveOwickiGries<>(mServices, mPredicateFactory, createCsToolkit(), program, getSettings())
					.createProofProducer(Function.identity());
		}

		@Override
		protected OwickiGriesSettings getSettings() {
			return new OwickiGriesSettings(OwickiGriesComputation.NAIVE, false, false);
		}

		@Override
		protected boolean requiresUnfoldingAndDifference() {
			return false;
		}
	}

	public static final class CrownsOG extends OGProofProducerTest {
		@Override
		protected IPetriNetProofProducer<SimpleAction, IPredicate>
				createProofProducer(final IPetriNet<SimpleAction, IPredicate> program) {
			return new CrownsOwickiGries<>(mServices, program, createCsToolkit(), mPredicateFactory,
					Function.identity());
		}

		@Override
		protected OwickiGriesSettings getSettings() {
			return new OwickiGriesSettings(OwickiGriesComputation.CROWN, false, false);
		}
	}

	public static final class GraphEmpireOG extends OGProofProducerTest {
		@Override
		protected IPetriNetProofProducer<SimpleAction, IPredicate>
				createProofProducer(final IPetriNet<SimpleAction, IPredicate> program) {
			return new GraphEmpireOwickiGries<>(mServices, program, createCsToolkit(), mPredicateFactory);
		}

		@Override
		protected OwickiGriesSettings getSettings() {
			return new OwickiGriesSettings(OwickiGriesComputation.SYMBOLIC_EXECUTION, false, false);
		}
	}

	public static final class EmpireAutomatonOG extends OGProofProducerTest {
		@Override
		protected IPetriNetProofProducer<SimpleAction, IPredicate>
				createProofProducer(final IPetriNet<SimpleAction, IPredicate> program) {
			return new EmpireAutomataOwickiGries<>(mServices, program, createCsToolkit(), mPredicateFactory,
					FocusComputation.UNFOCUSED);
		}

		@Override
		protected OwickiGriesSettings getSettings() {
			return new OwickiGriesSettings(OwickiGriesComputation.AUTOMATA, false, false);
		}

		@Override
		protected boolean requiresUnfoldingAndDifference() {
			return false;
		}
	}

	public static final class GlobalLegalFocusOG extends OGProofProducerTest {
		@Override
		protected IPetriNetProofProducer<SimpleAction, IPredicate>
				createProofProducer(final IPetriNet<SimpleAction, IPredicate> program) {
			return new EmpireAutomataOwickiGries<>(mServices, program, createCsToolkit(), mPredicateFactory,
					FocusComputation.GLOBAL);
		}

		@Override
		protected OwickiGriesSettings getSettings() {
			return new OwickiGriesSettings(OwickiGriesComputation.LEGAL_FOCUS, false, false);
		}

		@Override
		protected boolean requiresUnfoldingAndDifference() {
			return false;
		}
	}

	public static final class ModularLegalFocusOG extends OGProofProducerTest {
		@Override
		protected IPetriNetProofProducer<SimpleAction, IPredicate>
				createProofProducer(final IPetriNet<SimpleAction, IPredicate> program) {
			return new EmpireAutomataOwickiGries<>(mServices, program, createCsToolkit(), mPredicateFactory,
					FocusComputation.MODULAR);
		}

		@Override
		protected OwickiGriesSettings getSettings() {
			return new OwickiGriesSettings(OwickiGriesComputation.LEGAL_FOCUS, false, false);
		}

		@Override
		protected boolean requiresUnfoldingAndDifference() {
			return false;
		}
	}

	public static final class DirectedLegalFocusOG extends OGProofProducerTest {
		@Override
		protected IPetriNetProofProducer<SimpleAction, IPredicate>
				createProofProducer(final IPetriNet<SimpleAction, IPredicate> program) {
			return new DirectedLegalFocusOwickiGries<>(mServices, program, createCsToolkit());
		}

		@Override
		protected OwickiGriesSettings getSettings() {
			return new OwickiGriesSettings(OwickiGriesComputation.DIR_LEGAL_FOCUS, false, false);
		}

		@Override
		protected boolean requiresUnfoldingAndDifference() {
			return false;
		}
	}
}
