/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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
import java.util.Optional;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.junit.Before;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
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
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.NestedwordAutomatonAST;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.FactoryTestMethod;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.TestFactory;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Base class for Dynamic POR tests. Callers must only implemented the method
 * {@link #runTest(Path, AutomataTestFileAST, BoundedPetriNet, BoundedPetriNet, IIndependenceRelation)}.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public abstract class DynamicPORTestsBase implements IMessagePrinter {
	protected IUltimateServiceProvider mServices;
	protected AutomataLibraryServices mAutomataServices;
	protected ILogger mLogger;
	protected AutomataDefinitionInterpreter mInterpreter;

	protected abstract void runTest(final Path path, AutomataTestFileAST ast, NestedWordAutomaton<String, String> input,
			NestedWordAutomaton<String, String> expected, IIndependenceRelation<?, String> independence,
			IDisabling<String> disabling, IMembranes<String, String> membrane, IEnabling<String, String> enabling)
			throws AutomataLibraryException;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mAutomataServices = new AutomataLibraryServices(mServices);
		mLogger = mServices.getLoggingService().getLogger(getClass());
		mInterpreter = new AutomataDefinitionInterpreter(this, mLogger, mServices);
	}

	@TestFactory
	public Iterable<TestCase> createTests() throws IOException {
		final Path dir = Path.of(TestUtil.getPathFromTrunk("examples/Automata/dpor/"));
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

		NestedwordAutomatonAST inputAST = null;
		NestedwordAutomatonAST expectedAST = null;
		for (final var def : parsed.getAutomataDefinitions().getListOfAutomataDefinitions()) {
			if ("input".equals(def.getName())) {
				assert inputAST == null : "multiple inputs specified";
				inputAST = (NestedwordAutomatonAST) def;
			} else if ("expected".equals(def.getName())) {
				assert expectedAST == null : "multiple expected outputs specified";
				expectedAST = (NestedwordAutomatonAST) def;
			}
		}
		assert inputAST != null && expectedAST != null : "either input or expected is missing";

		mInterpreter.interpret(inputAST);
		mInterpreter.interpret(expectedAST);

		final var input = (NestedWordAutomaton<String, String>) mInterpreter.getAutomata().get("input");
		final var expected = (NestedWordAutomaton<String, String>) mInterpreter.getAutomata().get("expected");
		assert input != null && expected != null : "either input or expected is missing";

		final HashIndependence indep = new HashIndependence(extractCommutativity(path));
		final HashDisabling dis = new HashDisabling(extractDisabling(path));
		final HashMembranes mem = new HashMembranes(extractMembranes(path));
		final HashEnabling enab = new HashEnabling(extractEnabling(path));
		runTest(path, parsed, input, expected, indep, dis, mem, enab);
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
	
	private HashRelation<String, String> extractDisabling(final Path path) throws IOException {
		final String prefix = "//@ disabling ";

		final Optional<String> commLine;
		try (final var lines = Files.lines(path)) {
			commLine = lines.filter(l -> l.startsWith(prefix)).findFirst();
		}

		final HashRelation<String, String> result = new HashRelation<>();
		if (!commLine.isPresent()) {
			mLogger.info("no disabling specification found");
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

		mLogger.info("disabling: " + result.getSetOfPairs());
		return result;
	}
	
	private static final class HashDisabling implements IDisabling<String> {
		private final HashRelation<String, String> mRelation;
		//private final boolean mSymmetric;

		public HashDisabling(final HashRelation<String, String> relation) {
			mRelation = relation;
		}

		@Override
		public boolean disables(final String a, final String b) {
			return mRelation.containsPair(a, b) ? true : false;
		}
	}
	
	private HashRelation<String, String> extractMembranes(final Path path) throws IOException {
		final String prefix = "//@ membranes ";

		final Optional<String> commLine;
		try (final var lines = Files.lines(path)) {
			commLine = lines.filter(l -> l.startsWith(prefix)).findFirst();
		}

		final HashRelation<String, String> result = new HashRelation<>();
		if (!commLine.isPresent()) {
			mLogger.info("no membrane specification found");
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

		mLogger.info("membranes: " + result.getSetOfPairs());
		return result;
	}
	
	private static final class HashMembranes implements IMembranes<String, String> {
		private final HashRelation<String, String> mRelation;
		//private final boolean mSymmetric;

		public HashMembranes(final HashRelation<String, String> relation) {
			mRelation = relation;
		}

		@Override
		public Set<String> getMembraneSet(final String s) {
			return mRelation.getImage(s);
		}
	}
	
	private HashRelation<Pair<String, String>, String> extractEnabling(final Path path) throws IOException {
		final String prefix = "//@ enabling ";

		final Optional<String> commLine;
		try (final var lines = Files.lines(path)) {
			commLine = lines.filter(l -> l.startsWith(prefix)).findFirst();
		}

		final HashRelation<Pair<String, String>, String> result = new HashRelation<>();
		if (!commLine.isPresent()) {
			mLogger.info("no enabling specification found");
			return result;
		}

		final String relDescr = commLine.get().substring(prefix.length());
		final Pattern pairPattern = Pattern.compile("\\s*\\(([^,]+),([^\\)]+)\\)");
		final Matcher matcher = pairPattern.matcher(relDescr);
		while (matcher.find()) {
			String state = matcher.group(1).strip();
			final String letters = matcher.group(2).strip();
			final String first = letters.split(", ")[0];
			final String second = letters.split(", ")[1];
			System.out.println(state);
			if (state == "E") {state = "eps";}
			final Pair<String, String> pair = new Pair<>(state, first);
			result.addPair(pair, second);
		}

		mLogger.info("enabling: " + result.getSetOfPairs());
		return result;
	}
	
	private static final class HashEnabling implements IEnabling<String, String> {
		private final HashRelation<Pair<String, String>, String> mRelation;
		//private final boolean mSymmetric;

		public HashEnabling(final HashRelation<Pair<String, String>, String> relation) {
			mRelation = relation;
		}

		@Override
		public Set<String> getEnablingSet(final String s, final String a) {
			Pair<String, String> searchPair = new Pair<>(s,a);
			return mRelation.getImage(searchPair);
		}
	}
}
