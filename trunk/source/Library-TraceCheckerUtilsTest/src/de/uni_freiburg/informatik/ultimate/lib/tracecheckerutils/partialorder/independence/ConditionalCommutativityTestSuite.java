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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.junit.Before;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtParserUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.AutomataDefinitionInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.IMessagePrinter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.TestFileInterpreter.LoggerSeverity;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AutomataScriptParserRun;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.NestedwordAutomatonAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.PetriNetAutomatonAST;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.FactoryTestMethod;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.TestFactory;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Test suite for computation of conditional commutativity conditions.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public abstract class ConditionalCommutativityTestSuite implements IMessagePrinter {
	private static final String SOLVER_COMMAND = "z3 SMTLIB2_COMPLIANT=true -t:1000 -memory:2024 -smt2 -in";
	private static final LogLevel LOG_LEVEL = LogLevel.INFO;

	protected IUltimateServiceProvider mServices;
	protected AutomataLibraryServices mAutomataServices;
	protected ILogger mLogger;
	protected AutomataDefinitionInterpreter mInterpreter;
	protected ManagedScript mMgdScript;

	protected IIcfgSymbolTable mSymbolTable;
	protected BasicPredicateFactory mPredicateFactory;
	protected IHoareTripleChecker mHtc;
	protected final List<IPredicateUnifier> mUnifiers = new ArrayList<>();

	private long mStartTime = -1L;

	@TestFactory
	public Iterable<ConditionalCommutativityTestCase> createTests() throws IOException {
		final Path dir = Path.of(TestUtil.getPathFromTrunk("examples/concurrent/ats/conditional-comm"));
		try (final var files = Files.list(dir)) {
			return files.filter(file -> file.toString().endsWith(".ats")).map(ConditionalCommutativityTestCase::new)
					.sorted().collect(Collectors.toList());
		}
	}

	@Before
	public void setUp() {
		mStartTime = System.nanoTime();

		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mAutomataServices = new AutomataLibraryServices(mServices);
		mLogger = mServices.getLoggingService().getLogger(getClass());
		mInterpreter = new AutomataDefinitionInterpreter(this, mLogger, mServices);

		final var script = new HistoryRecordingScript(UltimateMocks.createSolver(SOLVER_COMMAND, LOG_LEVEL));
		script.setLogic(Logics.ALL);
		mMgdScript = new ManagedScript(mServices, script);
	}

	protected abstract void runTest(final Path path, final AutomataTestFileAST ast,
			final BoundedPetriNet<SimpleAction, IPredicate> program,
			final BoundedPetriNet<SimpleAction, IPredicate> refinedPetriNet,
			final BranchingProcess<SimpleAction, IPredicate> unfolding) throws AutomataLibraryException;

	private void runTestInternal(final Path path) throws IOException, AutomataLibraryException {
		mSymbolTable = setupSymbolTable(path);
		final var id2Action = parseActions(path);
		mPredicateFactory = new BasicPredicateFactory(mServices, mMgdScript, mSymbolTable);

		final AutomataTestFileAST parsed = parse(path);

		// find relevant ASTs
		PetriNetAutomatonAST programAST = null;
		final List<NestedwordAutomatonAST> proofASTs = new ArrayList<>();
		for (final var def : parsed.getAutomataDefinitions().getListOfAutomataDefinitions()) {
			if ("program".equals(def.getName())) {
				assert programAST == null : "multiple programs specified";
				programAST = (PetriNetAutomatonAST) def;
			} else if (def.getName().startsWith("proof")) {
				proofASTs.add((NestedwordAutomatonAST) def);
			}
		}
		assert programAST != null : "program is missing";

		// interpret ASTs
		mInterpreter.interpret(programAST);
		for (final var proofAST : proofASTs) {
			mInterpreter.interpret(proofAST);
		}

		// extract automata from AST
		final var petri = (BoundedPetriNet<String, String>) mInterpreter.getAutomata().get("program");
		final var automata = proofASTs.stream()
				.map(ast -> (NestedWordAutomaton<String, String>) mInterpreter.getAutomata().get(ast.getName()))
				.collect(Collectors.toList());
		assert petri != null : "program is missing";

		// replace strings with parsed transitions and predicates
		final var program = replaceActions(id2Action, petri);
		final var proofs =
				automata.stream().map(aut -> replaceActionsAndStates(id2Action, aut)).collect(Collectors.toList());

		// check proofs
		for (final var proof : proofs) {
			checkProof(proof);
		}

		// final var criterion = parseCriterion(path);
		// TODO parse criterion [after states have been created]
		// TODO parse condition generator [after predicates have been created]
		// TODO parse ctex
		// TODO parse ctex proof

		// compute difference of program and proofs
		// DifferencePetriNet<SimpleAction, IPredicate> difference = null;
		// for (final var proof : proofs) {
		// final var loopers = DifferencePairwiseOnDemand.determineUniversalLoopers(proof);
		// final var oldNet = difference == null ? program : difference;
		// final var initialTrueState = DataStructureUtils.getOneAndOnly(proof.getInitialStates(), "initial state");
		// difference = new DifferencePetriNet<>(mAutomataServices, oldNet,
		// new TotalizeNwa<>(proof, initialTrueState, false), loopers);
		// }
		// assert difference != null : "Difference can only be null if there no proofs, this is checked above";

		// final var finPrefix = new FinitePrefix<>(mAutomataServices, difference);
		// final var ctex = finPrefix.getAcceptingRun();
		// if (ctex != null) {
		// mLogger.warn("Unproven counterexample: %s", ctex);
		// }
		// assert ctex == null : "Proof is insufficient";
		//
		// final var bp = finPrefix.getResult();
		// final var constructedDifference = difference.getYetConstructedPetriNet();

		final long setupTime = System.nanoTime() - mStartTime;
		mLogger.info("ConditionalCommutativityTestSuite setup time: %s",
				CoreUtil.toTimeString(setupTime, TimeUnit.NANOSECONDS, TimeUnit.MILLISECONDS, 0));

		// runTest(path, parsed, program, constructedDifference, bp);
	}

	private void checkProof(final INestedWordAutomaton<SimpleAction, IPredicate> proof)
			throws AutomataLibraryException {
		assert NestedWordAutomataUtils.isFiniteAutomaton(proof) : "Proof must not have call or return transitions";
		assert new IsDeterministic<>(mAutomataServices, proof).getResult() : "Proof must be deterministic";

		for (final var initial : proof.getInitialStates()) {
			assert "true".equals(
					initial.getFormula().toString()) : "Initial state of proof automaton must be labeled 'true'";
		}

		for (final var accepting : proof.getFinalStates()) {
			assert "false".equals(
					accepting.getFormula().toString()) : "Accepting state of proof automaton must be labeled 'false'";
			// assert NestedWordAutomataUtils.isSinkState(proof, accepting) : "State 'false' should be a sink";
		}

		// assert new InductivityCheck<>(mServices, proof, false, true, mHtc).getResult();
	}

	private IIcfgSymbolTable setupSymbolTable(final Path path) throws IOException {
		final var symbolTable = new DefaultIcfgSymbolTable();

		final String prefix = "//@ variables ";
		final Optional<String> varLine;
		try (final var lines = Files.lines(path)) {
			varLine = lines.filter(l -> l.startsWith(prefix)).findFirst();
		}
		if (!varLine.isPresent()) {
			mLogger.info("no specification of program variables found");
			throw new IllegalArgumentException();
		}

		final String varDescr = varLine.get().substring(prefix.length());
		for (final var quantVar : parseVarDef(varDescr)) {
			final var pv = ProgramVarUtils.constructGlobalProgramVarPair(quantVar.getName(), quantVar.getSort(),
					mMgdScript, null);
			symbolTable.add(pv);
		}

		return symbolTable;
	}

	private TermVariable[] parseVarDef(final String varDef) {
		final var syntax = "(forall (" + varDef + ") true)";
		final var formula = (QuantifiedFormula) TermParseUtils.parseTerm(mMgdScript.getScript(), syntax);
		return formula.getVariables();
	}

	private Map<Integer, SimpleAction> parseActions(final Path path) throws IOException {
		final String prefix = "//@ semantics ";

		final List<String> actionLines;
		try (final var lines = Files.lines(path)) {
			actionLines = lines.filter(l -> l.startsWith(prefix)).collect(Collectors.toList());
		}

		if (actionLines.isEmpty()) {
			mLogger.warn("no actions found");
			return Collections.emptyMap();
		}

		final var result = new HashMap<Integer, SimpleAction>();
		final Pattern actionPattern =
				Pattern.compile("\\s*\\[(\\d+)\\]\\s+\\{([^\\}]*)\\}(\\s+\\[[^\\]]*\\]|)\\s+([^\\s].*)$");
		for (final var actionLine : actionLines) {
			final String actionDescr = actionLine.substring(prefix.length());
			final var matcher = actionPattern.matcher(actionDescr);

			final boolean found = matcher.find();
			assert found : "failed to parse action semantics: " + actionLine;

			final int id = Integer.parseUnsignedInt(matcher.group(1));
			final var assignedVarNames = Arrays.stream(matcher.group(2).split(",")).map(String::trim)
					.filter(s -> !s.isEmpty()).collect(Collectors.toSet());
			final var assignedVars = mSymbolTable.getGlobals().stream()
					.filter(pv -> assignedVarNames.contains(pv.getIdentifier())).collect(Collectors.toSet());

			final var auxVarString = matcher.group(3).trim();
			Set<TermVariable> auxVars;
			if (auxVarString.isEmpty()) {
				auxVars = Set.of();
			} else {
				auxVars = Set.of(parseVarDef(auxVarString.substring(0, auxVarString.length() - 1).substring(1)));
			}

			final String transformulaString = matcher.group(4);

			if (result.containsKey(id)) {
				throw new IllegalArgumentException("duplicate definition for action [" + id + "]");
			}

			final var action = new SimpleAction(id, parseTransformula(transformulaString, assignedVars, auxVars));
			result.put(id, action);
		}

		return result;
	}

	private UnmodifiableTransFormula parseTransformula(final String syntax, final Set<IProgramNonOldVar> assignedVars,
			final Set<TermVariable> auxVars) {
		final var termVars = Stream.concat(auxVars.stream(),
				Stream.concat(mSymbolTable.getGlobals().stream(),
						mSymbolTable.getGlobals().stream().map(IProgramNonOldVar::getOldVar))
						.map(IProgramVar::getTermVariable))
				.collect(Collectors.toSet());
		final var term = SmtParserUtils.parseWithVariables(syntax, mServices, mMgdScript, termVars);

		final var inVars = mSymbolTable.getGlobals().stream()
				.collect(Collectors.toMap(IProgramVar.class::cast, pv -> getOldTermVariable(pv, assignedVars)));
		final var outVars = mSymbolTable.getGlobals().stream()
				.collect(Collectors.toMap(IProgramVar.class::cast, IProgramVar::getTermVariable));
		final var builder = new TransFormulaBuilder(inVars, outVars, true, null, true, null, auxVars.isEmpty());
		for (final var av : auxVars) {
			builder.addAuxVar(av);
		}
		builder.setFormula(term);
		builder.setInfeasibility(Infeasibility.NOT_DETERMINED);

		return builder.finishConstruction(mMgdScript);
	}

	private static TermVariable getOldTermVariable(final IProgramNonOldVar pv,
			final Set<IProgramNonOldVar> assignedVars) {
		if (assignedVars.contains(pv)) {
			return pv.getOldVar().getTermVariable();
		}
		return pv.getTermVariable();
	}

	private AutomataTestFileAST parse(final Path path) throws FileNotFoundException {
		final String filename = path.getFileName().toString();
		final Reader reader = new BufferedReader(new FileReader(path.toFile()));
		return new AutomataScriptParserRun(mServices, mLogger, reader, filename, path.toString()).getResult();
	}

	private BoundedPetriNet<SimpleAction, IPredicate> replaceActions(final Map<Integer, SimpleAction> id2Action,
			final BoundedPetriNet<String, String> net) {
		final var parsedAlphabet =
				net.getAlphabet().stream().map(label -> parseAction(id2Action, label)).collect(Collectors.toSet());
		final var parsedNet = new BoundedPetriNet<SimpleAction, IPredicate>(mAutomataServices, parsedAlphabet, false);

		// copy places
		final var placeMap = new HashMap<String, IPredicate>();
		final var initialPlaces = net.getInitialPlaces();
		for (final var place : net.getPlaces()) {
			final var predPlace = mPredicateFactory.newDebugPredicate(place);
			placeMap.put(place, predPlace);
			parsedNet.addPlace(predPlace, initialPlaces.contains(place), net.isAccepting(place));
		}

		// copy transitions
		for (final var transition : net.getTransitions()) {
			final var predPreds =
					transition.getPredecessors().stream().map(placeMap::get).collect(ImmutableSet.collector());
			final var predSuccs =
					transition.getSuccessors().stream().map(placeMap::get).collect(ImmutableSet.collector());
			parsedNet.addTransition(parseAction(id2Action, transition.getSymbol()), predPreds, predSuccs);
		}

		return parsedNet;
	}

	private NestedWordAutomaton<SimpleAction, IPredicate> replaceActionsAndStates(
			final Map<Integer, SimpleAction> id2Action, final NestedWordAutomaton<String, String> aut) {
		final var parsedAlphabet = new VpAlphabet<>(
				aut.getAlphabet().stream().map(label -> parseAction(id2Action, label)).collect(Collectors.toSet()));
		final var parsedAut =
				new NestedWordAutomaton<SimpleAction, IPredicate>(mAutomataServices, parsedAlphabet, () -> null);

		// create predicate unifier for this iteration
		final var unifier = new PredicateUnifier(mLogger, mServices, mMgdScript, mPredicateFactory, mSymbolTable,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		mUnifiers.add(unifier);

		// parse states
		final var stateMap = new HashMap<String, IPredicate>();
		for (final var state : aut.getStates()) {
			final var parsedState = parsePredicate(state, unifier);
			stateMap.put(state, parsedState);
			parsedAut.addState(aut.isInitial(state), aut.isFinal(state), parsedState);
		}

		// parse transitions
		for (final var state : aut.getStates()) {
			for (final var transition : aut.internalSuccessors(state)) {
				parsedAut.addInternalTransition(stateMap.get(state), parseAction(id2Action, transition.getLetter()),
						stateMap.get(transition.getSucc()));
			}
		}

		return parsedAut;
	}

	private IPredicate parsePredicate(final String state, final IPredicateUnifier unifier) {
		final Term term = SmtParserUtils.parseWithVariables(state, mServices, mMgdScript, mSymbolTable);
		return unifier.getOrConstructPredicate(term);
	}

	private static SimpleAction parseAction(final Map<Integer, SimpleAction> id2Action, final String label) {
		final var pattern = Pattern.compile("^\\[(\\d+)\\]$");
		final var matcher = pattern.matcher(label);

		final boolean found = matcher.find();
		assert found : "Failed to parse action: " + label;

		final int id = Integer.parseUnsignedInt(matcher.group(1));
		if (!id2Action.containsKey(id)) {
			throw new IllegalArgumentException("Undefined action [" + id + "]");
		}
		return id2Action.get(id);
	}

	private IConditionalCommutativityCriterion<SimpleAction> parseCriterion(final Path path,
			final Map<Integer, SimpleAction> id2Action, final int iteration, final IPredicateUnifier unifier)
			throws IOException {
		final String prefix = "//@ criterion(" + iteration + ") ";

		final List<String> criterionLines;
		try (final var lines = Files.lines(path)) {
			criterionLines = lines.filter(l -> l.startsWith(prefix)).collect(Collectors.toList());
		}

		final var relation = new HashRelation3<IPredicate, SimpleAction, SimpleAction>();
		if (criterionLines.isEmpty()) {
			mLogger.warn("criterion always rejects");
		}

		final String statePattern = "\\(\\s*\\{[^\\}]*\\}\\,\\s*[^\\)]*\\)";
		final Pattern criterionPattern = Pattern.compile("\\s*(" + statePattern + ")\\s+\\[(\\d+)\\]\\s+\\[(\\d+)\\]$");
		for (final var criterionLine : criterionLines) {
			final String criterionDescr = criterionLine.substring(prefix.length());
			final var matcher = criterionPattern.matcher(criterionDescr);

			final boolean found = matcher.find();
			assert found : "failed to parse criterion: " + criterionLine;

			final IPredicate state = parseState(matcher.group(1), unifier);
			final var left = id2Action.get(Integer.parseUnsignedInt(matcher.group(2)));
			final var right = id2Action.get(Integer.parseUnsignedInt(matcher.group(3)));

			relation.addTriple(state, left, right);
			relation.addTriple(state, right, left);
		}

		return new TestCriterion<>(relation);
	}

	private IIndependenceConditionGenerator parseConditions(final Path path, final Map<Integer, SimpleAction> id2Action,
			final int iteration, final IPredicateUnifier unifier) throws IOException {
		final String prefix = "//@ condition(" + iteration + ") ";

		final List<String> conditionLines;
		try (final var lines = Files.lines(path)) {
			conditionLines = lines.filter(l -> l.startsWith(prefix)).collect(Collectors.toList());
		}

		final var map =
				new HashMap<Triple<IPredicate, UnmodifiableTransFormula, UnmodifiableTransFormula>, IPredicate>();
		if (conditionLines.isEmpty()) {
			mLogger.warn("no commutativity conditions specified");
		}

		final Pattern conditionPattern = Pattern.compile("\\s*(.*)\\s+\\[(\\d+)\\]\\s+\\[(\\d+)\\]\\s*:\\s*(.*)$");
		for (final var conditionLine : conditionLines) {
			final String criterionDescr = conditionLine.substring(prefix.length());
			final var matcher = conditionPattern.matcher(criterionDescr);

			final boolean found = matcher.find();
			assert found : "failed to parse condition: " + conditionLine;

			// TODO is it right to parse the context with the same unifier?!
			final IPredicate context = parsePredicate(matcher.group(1).trim(), unifier);
			final var left = id2Action.get(Integer.parseUnsignedInt(matcher.group(2)));
			final var right = id2Action.get(Integer.parseUnsignedInt(matcher.group(3)));
			final IPredicate condition = parsePredicate(matcher.group(4).trim(), unifier);

			map.put(new Triple<>(context, left.getTransformula(), right.getTransformula()), condition);
			map.put(new Triple<>(context, right.getTransformula(), left.getTransformula()), condition);
		}

		return new TestConditionGenerator(map);
	}

	private IPredicate parseState(final String stateString, final IPredicateUnifier unifier) {
		throw new UnsupportedOperationException("not implemented");
	}

	@Override
	public void printMessage(final Severity severityForResult, final LoggerSeverity severityForLogger,
			final String longDescr, final String shortDescr, final AtsASTNode node) {
		// TODO
		mLogger.warn(longDescr);
	}

	private static final class TestConditionGenerator implements IIndependenceConditionGenerator {
		private final Map<Triple<IPredicate, UnmodifiableTransFormula, UnmodifiableTransFormula>, IPredicate> mMap;

		private TestConditionGenerator(
				final Map<Triple<IPredicate, UnmodifiableTransFormula, UnmodifiableTransFormula>, IPredicate> map) {
			mMap = map;
		}

		@Override
		public IPredicate generateCondition(final IPredicate context, final UnmodifiableTransFormula a,
				final UnmodifiableTransFormula b) {
			return mMap.get(new Triple<>(context, a, b));
		}
	}

	private static final class TestCriterion<L> implements IConditionalCommutativityCriterion<L> {
		private final HashRelation3<IPredicate, L, L> mRelation;

		public TestCriterion(final HashRelation3<IPredicate, L, L> relation) {
			mRelation = relation;
		}

		@Override
		public boolean decide(final IPredicate state, IPredicate predicate, final L a, final L b) {
			return mRelation.containsTriple(state, a, b);
		}

		@Override
		public boolean decide(final IPredicate condition) {
			assert condition != null : "should not invoke criterion with null condition";
			return true;
		}
	}

	private final class ConditionalCommutativityTestCase implements Comparable<ConditionalCommutativityTestCase> {
		private final Path mPath;

		public ConditionalCommutativityTestCase(final Path path) {
			mPath = path;
		}

		@FactoryTestMethod
		public void run() throws AutomataLibraryException, IOException {
			runTestInternal(mPath);
		}

		@Override
		public String toString() {
			return mPath.getFileName().toString().replace(".", "_");
		}

		@Override
		public int compareTo(final ConditionalCommutativityTestCase other) {
			return mPath.compareTo(other.mPath);
		}
	}

	protected static final class SimpleAction implements IInternalAction {
		public static final String PROCEDURE = "Main";

		private final int mId;
		private final UnmodifiableTransFormula mTransFormula;

		public SimpleAction(final int id, final UnmodifiableTransFormula transFormula) {
			mId = id;
			mTransFormula = transFormula;
		}

		@Override
		public String getPrecedingProcedure() {
			return PROCEDURE;
		}

		@Override
		public String getSucceedingProcedure() {
			return getPrecedingProcedure();
		}

		@Override
		public UnmodifiableTransFormula getTransformula() {
			return mTransFormula;
		}

		@Override
		public int hashCode() {
			return Objects.hash(mId, mTransFormula);
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final SimpleAction other = (SimpleAction) obj;
			return mId == other.mId && Objects.equals(mTransFormula, other.mTransFormula);
		}

		@Override
		public String toString() {
			return "[" + mId + "]";
		}
	}
}
