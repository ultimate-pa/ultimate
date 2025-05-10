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
import java.util.function.Function;

import org.junit.runner.RunWith;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.OwickiGriesSettings.OwickiGriesComputation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.FactoryTestRunner;

@RunWith(FactoryTestRunner.class)
public abstract class OGProofProducerTest extends OwickiGriesTestSuite {
	@Override
	protected void runTest(final Path path, final AutomataTestFileAST ast,
			final BoundedPetriNet<SimpleAction, IPredicate> program,
			final BoundedPetriNet<SimpleAction, IPredicate> refinedPetriNet,
			final BranchingProcess<SimpleAction, IPredicate> unfolding) throws AutomataLibraryException, IOException {
		mLogger.info("Constructing Owicki-Gries proof for Petri program that %s.", program.sizeInformation());

		final var producer = createProofProducer(program);

		// feed the required information to the producer (simulate the CEGAR loop)
		for (int i = 0; i < mProofs.size(); ++i) {
			producer.refine(mUnifiers.get(i), mProofs.get(i), mBacktranslations.get(i));
		}
		producer.finalize(refinedPetriNet, unfolding);

		// let producer compute the proof
		assert producer.isReadyToComputeProof();
		final var annotation = producer.getOrComputeProof();

		// if assertions are enabled, the producers already carry out a validity check
		assert annotation != null;

		mLogger.info(
				"Computed Owicki-Gries annotation with %d ghost variables, %d ghost updates, and overall size %d\n%s",
				annotation.getGhostVariables().size(), annotation.getAssignmentMapping().size(), annotation.size(),
				annotation);

		// print proof producer statistics
		mLogger.info(producer.getStatistics());
	}

	protected CfgSmtToolkit createCsToolkit() {
		return new CfgSmtToolkit(computeModifiableGlobals(), mMgdScript, mSymbolTable, Set.of(SimpleAction.PROCEDURE),
				Map.of(), Map.of(), null, null, null);
	}

	protected abstract IPetriNetProofProducer<SimpleAction, IPredicate>
			createProofProducer(final IPetriNet<SimpleAction, IPredicate> program);

	protected abstract OwickiGriesSettings getSettings();

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
			return new EmpireAutomataOwickiGries<>(mServices, program, createCsToolkit(), mPredicateFactory);
		}

		@Override
		protected OwickiGriesSettings getSettings() {
			return new OwickiGriesSettings(OwickiGriesComputation.AUTOMATA, false, false);
		}
	}

	public static final class SeparateEmpiresOG extends OGProofProducerTest {
		@Override
		protected IPetriNetProofProducer<SimpleAction, IPredicate>
				createProofProducer(final IPetriNet<SimpleAction, IPredicate> program) {
			return new LegalFocusOwickiGries<>(mServices, program, createCsToolkit(), true);
		}

		@Override
		protected OwickiGriesSettings getSettings() {
			return new OwickiGriesSettings(OwickiGriesComputation.LEGAL_FOCUS, false, false);
		}
	}

	public static final class LegalFocusOG extends OGProofProducerTest {
		@Override
		protected IPetriNetProofProducer<SimpleAction, IPredicate>
				createProofProducer(final IPetriNet<SimpleAction, IPredicate> program) {
			return new LegalFocusOwickiGries<>(mServices, program, createCsToolkit(), false);
		}

		@Override
		protected OwickiGriesSettings getSettings() {
			return new OwickiGriesSettings(OwickiGriesComputation.LEGAL_FOCUS, false, false);
		}
	}
}
