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

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.junit.Before;
import org.junit.runner.RunWith;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.AutomataDefinitionInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.IMessagePrinter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.TestFileInterpreter.LoggerSeverity;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AutomataScriptParserRun;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.PetriNetAutomatonAST;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.FactoryTestMethod;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.FactoryTestRunner;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.TestFactory;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

@RunWith(FactoryTestRunner.class)
public class LiptonReductionTests implements IMessagePrinter {
	private IUltimateServiceProvider mServices;
	private AutomataLibraryServices mAutomataServices;
	private ILogger mLogger;
	private AutomataDefinitionInterpreter mInterpreter;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mAutomataServices = new AutomataLibraryServices(mServices);
		mLogger = mServices.getLoggingService().getLogger(getClass());
		mInterpreter = new AutomataDefinitionInterpreter(this, mLogger, mServices);
	}

	@TestFactory
	public Iterable<TestCase> createTests() throws IOException {
		final Path dir = Path.of(TestUtil.getPathFromTrunk("examples/Automata/PetriNet/lipton/"));
		try (var files = Files.list(dir)) {
			return files.map(TestCase::new).sorted().collect(Collectors.toList());
		}
	}

	private final class TestCase implements Comparable<TestCase> {
		private final Path mPath;

		public TestCase(final Path path) {
			mPath = path;
		}

		@FactoryTestMethod
		public void run() throws PetriNetNot1SafeException, AutomataOperationCanceledException, IOException {
			runTest(mPath);
		}

		@Override
		public String toString() {
			return mPath.getFileName().toString();
		}

		@Override
		public int compareTo(final TestCase other) {
			return mPath.compareTo(other.mPath);
		}
	}

	private void runTest(final Path path)
			throws PetriNetNot1SafeException, AutomataOperationCanceledException, IOException {
		final AutomataTestFileAST parsed = parse(path);

		PetriNetAutomatonAST inputAST = null;
		PetriNetAutomatonAST expectedAST = null;
		for (final var def : parsed.getAutomataDefinitions().getListOfAutomataDefinitions()) {
			if ("initial".equals(def.getName())) {
				assert inputAST == null : "multiple inputs specified";
				inputAST = (PetriNetAutomatonAST) def;
			} else if ("expected".equals(def.getName())) {
				assert expectedAST == null : "multiple expected outputs specified";
				expectedAST = (PetriNetAutomatonAST) def;
			}
		}
		assert inputAST != null && expectedAST != null : "either input or expected is missing";

		mInterpreter.interpret(inputAST);
		mInterpreter.interpret(expectedAST);

		final var input = (BoundedPetriNet<String, String>) mInterpreter.getAutomata().get("initial");
		final var expected = (BoundedPetriNet<String, String>) mInterpreter.getAutomata().get("expected");
		assert input != null && expected != null : "either input or expected is missing";

		final HashIndependence indep = new HashIndependence(extractCommutativity(path));
		final var reduction = new LiptonReduction<>(mAutomataServices, input, CompositionFactory.INSTANCE,
				CopyPlaceFactory.INSTANCE, indep, PostScriptChecker.INSTANCE, null);
		reduction.performReduction();
		final BoundedPetriNet<String, String> actual = reduction.getResult();

		assert areEqual(expected, actual) : "PNs differ, expected " + expected + " but actual was " + actual;
	}

	private AutomataTestFileAST parse(final Path path) throws FileNotFoundException {
		final String filename = path.getFileName().toString();
		final Reader reader = new BufferedReader(new FileReader(path.toFile()));
		return new AutomataScriptParserRun(mServices, mLogger, reader, filename, path.toString()).getResult();
	}

	private HashRelation<String, String> extractCommutativity(final Path path) throws IOException {
		final String prefix = "//@ commutativity ";

		final Optional<String> commLine;
		try (final var lines = Files.lines(path)) {
			commLine = lines.filter(l -> l.startsWith(prefix)).findFirst();
		}

		final HashRelation<String, String> result = new HashRelation<>();
		if (!commLine.isPresent()) {
			mLogger.info("no commutativity specification found");
			return result;
		}

		final String relDescr = commLine.get().substring(prefix.length());
		final Pattern pairPattern = Pattern.compile("\\s*\\(([^,]+),([^\\)]+)\\)");
		final Matcher matcher = pairPattern.matcher(relDescr);
		while (matcher.find()) {
			final String left = matcher.group(1).strip();
			final String right = matcher.group(2).strip();
			result.addPair(left, right);
		}

		mLogger.info("commutativity: " + result.getSetOfPairs());
		return result;
	}

	@Override
	public void printMessage(final Severity severityForResult, final LoggerSeverity severityForLogger,
			final String longDescr, final String shortDescr, final AtsASTNode node) {
		// TODO
		mLogger.warn(longDescr);
	}

	private static final class CompositionFactory implements ICompositionFactory<String> {
		public static final CompositionFactory INSTANCE = new CompositionFactory();

		@Override
		public boolean isSequentiallyComposable(final String l1, final String l2) {
			return true;
		}

		@Override
		public boolean isParallelyComposable(final List<String> letters) {
			return true;
		}

		@Override
		public String composeSequential(final String first, final String second) {
			return first + second;
		}

		@Override
		public String composeParallel(final List<String> letters) {
			return "(" + letters.stream().collect(Collectors.joining("+")) + ")";
		}
	}

	private static final class CopyPlaceFactory implements ICopyPlaceFactory<String> {
		public static final CopyPlaceFactory INSTANCE = new CopyPlaceFactory();

		private final Map<String, Integer> mCopyCounter = new HashMap<>();
		private int freshCounter;

		@Override
		public String copyPlace(final String oldPlace) {
			final int oldCount = mCopyCounter.getOrDefault(oldPlace, 0);
			mCopyCounter.put(oldPlace, oldCount + 1);
			return oldPlace + "_copy" + (oldCount + 1);
		}

		@Override
		public String createFreshPlace() {
			freshCounter++;
			return "fresh" + freshCounter;
		}
	}

	private static final class HashIndependence implements IIndependenceRelation<Set<String>, String> {
		private final HashRelation<String, String> mRelation;
		private final boolean mSymmetric;

		public HashIndependence(final HashRelation<String, String> relation) {
			mRelation = relation;
			mSymmetric = isSymmetric(relation);
		}

		private static boolean isSymmetric(final HashRelation<String, String> relation) {
			for (final var pair : relation) {
				if (!relation.containsPair(pair.getValue(), pair.getKey())) {
					return false;
				}
			}
			return true;
		}

		@Override
		public boolean isSymmetric() {
			return mSymmetric;
		}

		@Override
		public boolean isConditional() {
			return false;
		}

		@Override
		public boolean contains(final Set<String> state, final String a, final String b) {
			return mRelation.containsPair(a, b);
		}
	}

	private static final class PostScriptChecker implements IPostScriptChecker<String, String> {
		public static final PostScriptChecker INSTANCE = new PostScriptChecker();

		@Override
		public boolean isPostScript(final IPetriNet<String, String> net,
				final Set<ITransition<String, String>> transitions) {
			return false;
		}
	}

	private boolean areEqual(final BoundedPetriNet<String, String> first,
			final BoundedPetriNet<String, String> second) {
		if (!first.getAlphabet().equals(second.getAlphabet())) {
			mLogger.warn("alphabet differs: %s != %s", first.getAlphabet(), second.getAlphabet());
			return false;
		}

		if (!first.getPlaces().equals(second.getPlaces())) {
			mLogger.warn("places differ");
			return false;
		}

		if (!first.getInitialPlaces().equals(second.getInitialPlaces())) {
			mLogger.warn("initial places differ");
			return false;
		}

		if (!first.getAcceptingPlaces().equals(second.getAcceptingPlaces())) {
			mLogger.warn("accepting places differ");
			return false;
		}

		if (first.getTransitions().size() != second.getTransitions().size()) {
			mLogger.warn("transition count differs");
			return false;
		}

		for (final var trans1 : first.getTransitions()) {
			boolean found = false;
			for (final var trans2 : second.getTransitions()) {
				if (!trans1.getSymbol().equals(trans2.getSymbol())) {
					continue;
				}
				if (!first.getPredecessors(trans1).equals(second.getPredecessors(trans2))) {
					continue;
				}
				if (!first.getSuccessors(trans1).equals(second.getSuccessors(trans2))) {
					continue;
				}
				found = true;
			}
			if (!found) {
				mLogger.warn("no matching transition for " + trans1);
				return false;
			}
		}

		return true;
	}
}
