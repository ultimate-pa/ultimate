package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries;

import static org.hamcrest.CoreMatchers.equalTo;
import static org.junit.Assert.assertEquals;
import static org.junit.Assume.assumeThat;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.Set;
import java.util.stream.Collectors;

import org.junit.runner.RunWith;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.crown.PlacesCoRelation;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.EmpireToOwickiGries;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.EmpireValidityCheck;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.PetriOwickiGries;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire.Territory;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.FactoryTestRunner;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

@RunWith(FactoryTestRunner.class)
public class EmpireToOwickiGriesTest extends OwickiGriesTestSuite {
	@Override
	protected void runTest(final Path path, final AutomataTestFileAST ast,
			final BoundedPetriNet<SimpleAction, IPredicate> program,
			final BoundedPetriNet<SimpleAction, IPredicate> refinedPetriNet,
			final BranchingProcess<SimpleAction, IPredicate> unfolding) throws AutomataLibraryException, IOException {

		final var unifier = mUnifiers.get(0);
		final var implicationChecker = new MonolithicImplicationChecker(mServices, mMgdScript);
		final var modifiableGlobals = computeModifiableGlobals();

		final var empire = new EmpireAnnotationParser<>(mProgramPlaceMap::get, s -> parsePredicate(s, unifier),
				unifier::getOrConstructPredicateForConjunction).parse(computeEmpirePath(path));
		mLogger.info("Parsed Empire annotation:\n%s", empire);

		final var assertionPlaces =
				mProofs.stream().map(nwa -> nwa.getStates()).flatMap(Set::stream).collect(Collectors.toSet());
		final var predicatePlaceMap = new HashMap<IPredicate, IPredicate>();
		for (final Pair<Territory<IPredicate>, IPredicate> pair : empire.getEmpire()) {
			final var law = pair.getSecond();
			for (final IPredicate iPredicate : assertionPlaces) {
				if (law.getFormula().equals(iPredicate.getFormula())) {
					predicatePlaceMap.put(law, iPredicate);
				}
			}
		}
		final var empireCheck = new EmpireValidityCheck<>(mServices, mMgdScript, implicationChecker, mPredicateFactory,
				program, unfolding.getNet(), modifiableGlobals, empire, predicatePlaceMap, assertionPlaces,
				new PlacesCoRelation<>(unfolding));
		assumeThat("Given empire annotation is not valid", empireCheck.getValidity(), equalTo(Validity.VALID));

		final var empireToOwickiGries = new EmpireToOwickiGries<>(mServices, mMgdScript, program, mSymbolTable,
				Set.of(SimpleAction.PROCEDURE), empire);
		final var owickiGries = empireToOwickiGries.getAnnotation();
		mLogger.info("Computed Owicki-Gries annotation:\n%s", owickiGries);

		final var owickiGriesCheck = new OwickiGriesValidityCheck<>(mServices, mMgdScript, modifiableGlobals,
				owickiGries, PetriOwickiGries.getCoMarkedPlaces(unfolding));
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
