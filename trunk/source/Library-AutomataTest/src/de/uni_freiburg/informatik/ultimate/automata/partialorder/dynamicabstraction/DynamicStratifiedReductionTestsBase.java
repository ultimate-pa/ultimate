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
package de.uni_freiburg.informatik.ultimate.automata.partialorder.dynamicabstraction;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
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
import de.uni_freiburg.informatik.ultimate.util.datastructures.BidirectionalMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PowersetLattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.UpsideDownLattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Quad;

/**
 * Base class for Dynamic Stratified Reduction tests. Callers must only implemented the method
 * {@link #runTest(Path, AutomataTestFileAST, NestedWordAutomaton, NestedWordAutomaton, IIndependenceInducedByAbstraction)}.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public abstract class DynamicStratifiedReductionTestsBase implements IMessagePrinter {
	protected IUltimateServiceProvider mServices;
	protected AutomataLibraryServices mAutomataServices;
	protected ILogger mLogger;
	protected AutomataDefinitionInterpreter mInterpreter;

	protected abstract void runTest(final Path path, AutomataTestFileAST ast, NestedWordAutomaton<String, String> input,
			NestedWordAutomaton<String, String> expected,
			IIndependenceInducedByAbstraction<String, String, Set<String>> independence,
			IProofManager<Set<String>, String> proofManager, ILattice<Set<String>> lattice)
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
		final Path dir = Path.of(TestUtil.getPathFromTrunk("examples/Automata/dynamic-abstractions/"));
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

		final IIndependenceInducedByAbstraction<String, String, Set<String>> indep = extractCommutativity(path);
		final IProofManager<Set<String>, String> proofManager = new StringProofManager(extractProofs(path));

		final ILattice<Set<String>> lattice = new UpsideDownLattice<>(new PowersetLattice<>(extractProofVars(path)));

		runTest(path, parsed, input, expected, indep, proofManager, lattice);
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

	private static List<Set<String>> extractProofs(final Path path) throws IOException {
		final String prefix = "//@ proof variables ";

		final Optional<String> proofLine;
		try (final var lines = Files.lines(path)) {
			proofLine = lines.filter(l -> l.startsWith(prefix)).findFirst();
		}

		if (!proofLine.isPresent()) {
			throw new AssertionError("no proof variables specification found");
		}

		final String relDescr = proofLine.get().substring(prefix.length());
		final String[] proofDescrs = relDescr.split("\\|");
		final var result = new ArrayList<Set<String>>();
		for (final var proof : proofDescrs) {
			final var variables = Arrays.stream(proof.split(",")).map(String::strip).collect(Collectors.toSet());
			result.add(variables);
		}
		return result;
	}

	// TODO überprüfen
	private Set<String> extractProofVars(final Path path) throws IOException {
		final Iterator<Set<String>> varList = extractProofs(path).iterator();
		final Set<String> allVars = new HashSet<>();
		varList.forEachRemaining((varSet) -> allVars.addAll(varSet));
		return allVars;
	}

	private <S> IIndependenceInducedByAbstraction<S, String, Set<String>> extractCommutativity(final Path path)
			throws IOException {
		final String prefix = "//@ commutativity ";

		final Optional<String> commLine;
		try (final var lines = Files.lines(path)) {
			commLine = lines.filter(l -> l.startsWith(prefix)).findFirst();
		}

		if (!commLine.isPresent()) {
			mLogger.info("no commutativity specification found");
			return new HashIndependenceByAbstraction<>(Map.of());
		}

		final HashMap<Set<String>, HashRelation<String, String>> result = new HashMap<>();

		final String relDescr = commLine.get().substring(prefix.length());
		final Pattern triplePattern = Pattern.compile("\\s*\\(\\{([^\\}]*)\\},([^,]+),([^\\)]+)\\)");
		final Matcher matcher = triplePattern.matcher(relDescr);
		while (matcher.find()) {
			final Set<String> abstr =
					Arrays.stream(matcher.group(1).strip().split(" ")).map(String::strip).collect(Collectors.toSet());
			final String left = matcher.group(2).strip();
			final String right = matcher.group(3).strip();

			result.computeIfAbsent(abstr, x -> new HashRelation<>()).addPair(left, right);
		}

		mLogger.info("commutativity:");
		for (final var entry : result.entrySet()) {
			mLogger.info("\t%s ::= %s", entry.getKey(), entry.getValue().getSetOfPairs());
		}

		return new HashIndependenceByAbstraction<>(result.entrySet().stream()
				.collect(Collectors.toMap(Map.Entry::getKey, e -> new HashIndependence<>(e.getValue()))));
	}

	private static final class HashIndependenceByAbstraction<S>
			implements IIndependenceInducedByAbstraction<S, String, Set<String>> {

		private final IIndependenceRelation<S, String> mEmptyIndependence =
				new HashIndependence<>(new HashRelation<>());
		private final Map<Set<String>, IIndependenceRelation<S, String>> mMap;

		public HashIndependenceByAbstraction(final Map<Set<String>, IIndependenceRelation<S, String>> map) {
			mMap = map;
		}

		@Override
		public IIndependenceRelation<S, String> getInducedIndependence(final Set<String> freeVariables) {
			final var result = mMap.get(freeVariables);
			if (result == null) {
				// If no independence is given, assume nothing commutes
				return mEmptyIndependence;
			}
			return result;
		}
	}

	private static final class HashIndependence<S> implements IIndependenceRelation<S, String> {
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
		public Dependence isIndependent(final S state, final String a, final String b) {
			return mRelation.containsPair(a, b) ? Dependence.INDEPENDENT : Dependence.DEPENDENT;
		}
	}

	private static final class StringProofManager implements IProofManager<Set<String>, String> {
		private final List<Set<String>> mProofs;

		public StringProofManager(final List<Set<String>> proofs) {
			mProofs = proofs;
		}

		private String[] getProofStates(final String state) {
			final var splitStates = state.split("\\|");
			assert splitStates.length == mProofs.size() : "Got state of " + splitStates.length
					+ " proofs, but expected " + mProofs.size();
			return splitStates;
		}

		@Override
		public boolean isProvenState(final String state) {
			return Arrays.asList(getProofStates(state)).contains("false");
		}

		@Override
		public Set<String> chooseResponsibleAbstraction(final String state) {
			// always chooses the proof with the minimal index
			// TODO @Veronika: Customize this if necessary
			final int result = Arrays.asList(getProofStates(state)).indexOf("false");
			if (result < 0) {
				throw new IllegalStateException("No proof can be made responsible in state " + state);
			}
			return mProofs.get(result);
		}
	}

	protected class AlphabeticOrder<S> implements IDfsOrder<String, S> {
		@Override
		public Comparator<String> getOrder(final S state) {
			return Comparator.naturalOrder();
		}

		@Override
		public boolean isPositional() {
			return false;
		}
	}

	protected class StratifiedStringFactory implements IStratifiedStateFactory<String, String, String, Set<String>> {

		private final BidirectionalMap<String, Quad<String, ImmutableSet<String>, AbstractionLevel<Set<String>>, AbstractionLevel<Set<String>>>> mMap =
				new BidirectionalMap<>();
		private int mCounter;

		@Override
		public String createEmptyStackState() {
			return "###empty###";
		}

		@Override
		public String createStratifiedState(final String state, final ImmutableSet<String> sleepset,
				final AbstractionLevel<Set<String>> level, final AbstractionLevel<Set<String>> limit) {
			final var quad = new Quad<>(state, sleepset, level, limit);
			final var existing = mMap.inverse().get(quad);
			if (existing != null) {
				return existing;
			}

			// TODO @Veronika It may be nicer to include the parameters in the name.
			final var name = "s" + mCounter;
			mCounter++;
			mMap.put(name, quad);
			return name;
		}

		@Override
		public String getOriginalState(final String state) {
			return mMap.get(state).getFirst();
		}

		@Override
		public ImmutableSet<String> getSleepSet(final String state) {
			return mMap.get(state).getSecond();
		}

		@Override
		public AbstractionLevel<Set<String>> getAbstractionLevel(final String state) {
			return mMap.get(state).getThird();
		}

		@Override
		public void addToAbstractionLevel(final String state, final Set<String> variables) {
			final AbstractionLevel<Set<String>> level = mMap.get(state).getThird();
			level.addToAbstractionLevel(variables);
			mMap.replace(state, new Quad<>(mMap.get(state).getFirst(), mMap.get(state).getSecond(), level,
					mMap.get(state).getFourth()));
		}

		@Override
		public AbstractionLevel<Set<String>> getAbstractionLimit(final String state) {
			return mMap.get(state).getFourth();
		}

		@Override
		public void addToAbstractionLimit(final String state, final Set<String> variables) {
			final AbstractionLevel<Set<String>> limit = mMap.get(state).getFourth();
			limit.addToAbstractionLevel(variables);
			mMap.replace(state, new Quad<>(mMap.get(state).getFirst(), mMap.get(state).getSecond(),
					mMap.get(state).getThird(), limit));
		}

		@Override
		public boolean isLoopCopy(final String state) {
			return mMap.get(state).getFourth().isLocked();
		}

		@Override
		public void defineAbstractionLevel(final String state) {
			final AbstractionLevel<Set<String>> level = mMap.get(state).getThird();
			level.lock();
			mMap.replace(state, new Quad<>(mMap.get(state).getFirst(), mMap.get(state).getSecond(), level,
					mMap.get(state).getFourth()));

		}

		@Override
		public void setSleepSet(final String state, final ImmutableSet<String> sleepset) {
			mMap.replace(state, new Quad<>(mMap.get(state).getFirst(), sleepset, mMap.get(state).getThird(),
					mMap.get(state).getFourth()));
		}
	}
}
