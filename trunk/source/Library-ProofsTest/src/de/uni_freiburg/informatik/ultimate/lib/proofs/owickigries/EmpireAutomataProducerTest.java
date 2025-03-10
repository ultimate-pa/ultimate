package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries;

import java.io.IOException;
import java.nio.file.Path;
import java.util.Map;
import java.util.Set;

import org.junit.runner.RunWith;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireAutomataConstruction;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.FactoryTestRunner;

@RunWith(FactoryTestRunner.class)
public class EmpireAutomataProducerTest extends OwickiGriesTestSuite {

	@Override
	protected void runTest(final Path path, final AutomataTestFileAST ast,
			final BoundedPetriNet<SimpleAction, IPredicate> program,
			final BoundedPetriNet<SimpleAction, IPredicate> refinedPetriNet,
			final BranchingProcess<SimpleAction, IPredicate> unfolding) throws AutomataLibraryException, IOException {
		mLogger.info("Constructing Owicki-Gries proof for Petri program that %s.", program.sizeInformation());
		final var csToolkit = createCsToolkit();
		final var automatonConstruction = new EmpireAutomataConstruction<>(mServices, program,
				csToolkit.getManagedScript(), mSymbolTable, csToolkit.getModifiableGlobalsTable(), mPredicateFactory);

		// feed the required information to the producer (simulate the CEGAR loop)
		for (int i = 0; i < mProofs.size(); ++i) {
			automatonConstruction.refine(mUnifiers.get(i), mProofs.get(i), mBacktranslations.get(i));
		}

		// let producer compute the proof
		final var annotation = automatonConstruction.getOrComputeAutomaton();

		// if assertions are enabled, the producers already carry out a validity check
		assert annotation != null;

	}

	protected CfgSmtToolkit createCsToolkit() {
		return new CfgSmtToolkit(computeModifiableGlobals(), mMgdScript, mSymbolTable, Set.of(SimpleAction.PROCEDURE),
				Map.of(), Map.of(), null, null, null);
	}
}
