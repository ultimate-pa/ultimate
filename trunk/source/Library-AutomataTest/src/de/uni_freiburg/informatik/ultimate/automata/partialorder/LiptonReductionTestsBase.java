/*
 * Copyright (C) 2021-2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021-2022 University of Freiburg
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
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.junit.Before;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
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
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.TestFactory;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Base class for Lipton reduction tests. Callers must only implemented the method
 * {@link #runTest(Path, AutomataTestFileAST, BoundedPetriNet, BoundedPetriNet, IIndependenceRelation)}.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public abstract class LiptonReductionTestsBase implements IMessagePrinter {
	protected IUltimateServiceProvider mServices;
	protected AutomataLibraryServices mAutomataServices;
	protected ILogger mLogger;
	protected AutomataDefinitionInterpreter mInterpreter;

	protected abstract void runTest(final Path path, AutomataTestFileAST ast, BoundedPetriNet<String, String> input,
			BoundedPetriNet<String, String> expected, IIndependenceRelation<Set<String>, String> independence,
			IPostScriptChecker<String, String> ps) throws AutomataLibraryException;

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
		public void run() throws AutomataLibraryException, IOException {
			runTestInternal(mPath);
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

	private void runTestInternal(final Path path) throws AutomataLibraryException, IOException {
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
		final PostScriptChecker psc = new PostScriptChecker(extractPostScript(path));
		runTest(path, parsed, input, expected, indep, psc);
	}

	@Override
	public void printMessage(final Severity severityForResult, final LoggerSeverity severityForLogger,
			final String longDescr, final String shortDescr, final AtsASTNode node) {
		// TODO
		mLogger.warn(longDescr);
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

	private Set<String> extractPostScript(final Path path) throws IOException {
		final String prefix = "//@ not-stuck ";

		final Optional<String> psLine;
		try (final var lines = Files.lines(path)) {
			psLine = lines.filter(l -> l.startsWith(prefix)).findFirst();
		}

		if (!psLine.isPresent()) {
			mLogger.info("no post-script specification found");
			return Collections.emptySet();
		}

		final var result = new HashSet<String>();

		final String relDescr = psLine.get().substring(prefix.length());
		final Pattern placePattern = Pattern.compile("\\s*\"([^\"]+)\"");
		final Matcher matcher = placePattern.matcher(relDescr);
		while (matcher.find()) {
			final String place = matcher.group(1).strip();
			result.add(place);
		}

		mLogger.info("post-script (not-stuck places): " + result);
		return result;
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
		public Dependence isIndependent(final Set<String> state, final String a, final String b) {
			return mRelation.containsPair(a, b) ? Dependence.INDEPENDENT : Dependence.DEPENDENT;
		}
	}

	protected static final class CompositionFactory implements ICompositionFactory<String> {
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

	protected static final class CopyPlaceFactory implements ICopyPlaceFactory<String> {
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

	protected static final class PostScriptChecker implements IPostScriptChecker<String, String> {
		private final Set<String> mNotStuckPlaces;

		public PostScriptChecker(final Set<String> notStuckPlaces) {
			mNotStuckPlaces = notStuckPlaces;
		}

		@Override
		public boolean mightGetStuck(final IPetriNet<String, String> petriNet, final String place) {
			return !mNotStuckPlaces.contains(place);
		}

		@Override
		public boolean isPostScript(final IPetriNet<String, String> net,
				final Set<Transition<String, String>> transitions) {
			throw new UnsupportedOperationException();
		}
	}
}
