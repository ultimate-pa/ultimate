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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries;

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
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.junit.Before;
import org.junit.runner.RunWith;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsTotal;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.DifferencePairwiseOnDemand;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.DifferencePetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.FinitePrefix;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtParserUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.predicates.InductivityCheck;
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
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.FactoryTestRunner;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.TestFactory;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Test suite for computation of Owicki-Gries annotations for Petri programs.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
@RunWith(FactoryTestRunner.class)
public class OwickiGriesTestSuite implements IMessagePrinter {
	private static final String SOLVER_COMMAND = "z3 SMTLIB2_COMPLIANT=true -t:1000 -memory:2024 -smt2 -in";
	private static final LogLevel LOG_LEVEL = LogLevel.INFO;

	protected IUltimateServiceProvider mServices;
	protected AutomataLibraryServices mAutomataServices;
	protected ILogger mLogger;
	protected AutomataDefinitionInterpreter mInterpreter;
	protected ManagedScript mMgdScript;

	protected IIcfgSymbolTable mSymbolTable;
	protected BasicPredicateFactory mPredicateFactory;
	protected PredicateUnifier mUnifier;
	protected IHoareTripleChecker mHtc;

	@TestFactory
	public Iterable<OwickiGriesTestCase> createTests() throws IOException {
		final Path dir = Path.of(TestUtil.getPathFromTrunk("examples/concurrent/OwickiGries/PetriPrograms"));
		try (final var files = Files.list(dir)) {
			return files.map(OwickiGriesTestCase::new).sorted().collect(Collectors.toList());
		}
	}

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mAutomataServices = new AutomataLibraryServices(mServices);
		mLogger = mServices.getLoggingService().getLogger(getClass());
		mInterpreter = new AutomataDefinitionInterpreter(this, mLogger, mServices);

		final var script = new HistoryRecordingScript(UltimateMocks.createSolver(SOLVER_COMMAND, LOG_LEVEL));
		script.setLogic(Logics.ALIA);
		mMgdScript = new ManagedScript(mServices, script);
	}

	public void runTest(final Path path, final AutomataTestFileAST ast,
			final BoundedPetriNet<SimpleAction, IPredicate> program,
			final BoundedPetriNet<SimpleAction, IPredicate> refinedPetriNet,
			final BranchingProcess<SimpleAction, IPredicate> unfolding) throws AutomataLibraryException {
		// construct Owicki-Gries annotation
		final var floydHoare = new PetriFloydHoare<>(mServices, mMgdScript, mSymbolTable,
				Set.of(SimpleAction.PROCEDURE), unfolding, program, List.of(mUnifier), true, true);
		final Map<Marking<IPredicate>, IPredicate> petriFloydHoare = floydHoare.getResult();
		final var construction = new OwickiGriesConstruction<>(mServices, mMgdScript, mSymbolTable,
				Set.of(SimpleAction.PROCEDURE), program, petriFloydHoare, true);
		final var annotation = construction.getResult();

		// check validity of annotation
		final var check = new OwickiGriesValidityCheck<>(mServices, mMgdScript, mHtc, annotation,
				construction.getCoMarkedPlaces());

		if (!check.isValid()) {
			throw new AssertionError("Invalid Owicki-Gries annotation");
		}
	}

	private void runTestInternal(final Path path) throws IOException, AutomataLibraryException {
		mSymbolTable = setupSymbolTable(path);
		final var id2Action = parseActions(path);
		mPredicateFactory = new BasicPredicateFactory(mServices, mMgdScript, mSymbolTable);
		mUnifier = new PredicateUnifier(mLogger, mServices, mMgdScript, mPredicateFactory, mSymbolTable,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		final var modifiesRelation = new HashRelation<String, IProgramNonOldVar>();
		for (final var pv : mSymbolTable.getGlobals()) {
			modifiesRelation.addPair(SimpleAction.PROCEDURE, pv);
		}
		final var modifiableGlobals = new ModifiableGlobalsTable(modifiesRelation);
		mHtc = new MonolithicHoareTripleChecker(mMgdScript, modifiableGlobals);

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
		assert programAST != null && !proofASTs.isEmpty() : "either program or proof is missing";

		// interpret AST
		mInterpreter.interpret(programAST);
		for (final var proofAST : proofASTs) {
			mInterpreter.interpret(proofAST);
		}

		// extract automata from AST
		final var petri = (BoundedPetriNet<String, String>) mInterpreter.getAutomata().get("program");
		final var automata = proofASTs.stream()
				.map(ast -> (NestedWordAutomaton<String, String>) mInterpreter.getAutomata().get(ast.getName()))
				.collect(Collectors.toList());
		assert petri != null && !automata.isEmpty() : "either program or proof is missing";

		// replace strings with parsed transitions and predicates
		final var program = replaceActions(id2Action, petri);
		final var proofs =
				automata.stream().map(aut -> replaceActionsAndStates(id2Action, aut)).collect(Collectors.toList());

		// check proofs
		for (final var proof : proofs) {
			checkProof(proof);
		}

		// compute difference of program and proofs
		DifferencePetriNet<SimpleAction, IPredicate> difference = null;
		for (final var proof : proofs) {
			final var loopers = DifferencePairwiseOnDemand.determineUniversalLoopers(proof);
			final var oldNet = difference == null ? program : difference;
			difference = new DifferencePetriNet<>(mAutomataServices, oldNet, proof, loopers);
		}
		assert difference != null : "Difference can only be null if there no proofs, this is checked above";

		final var bp = new FinitePrefix<>(mAutomataServices, difference).getResult();
		final var constructedDifference = difference.getYetConstructedPetriNet();

		runTest(path, parsed, program, constructedDifference, bp);
	}

	private void checkProof(final INestedWordAutomaton<SimpleAction, IPredicate> proof)
			throws AutomataLibraryException {
		assert NestedWordAutomataUtils.isFiniteAutomaton(proof) : "Proof must not have call or return transitions";
		assert new IsDeterministic<>(mAutomataServices, proof).getResult() : "Proof must be deterministic";
		assert new IsTotal<>(mAutomataServices, proof).getResult() : "Proof must be total";

		for (final var initial : proof.getInitialStates()) {
			assert "true".equals(
					initial.getFormula().toString()) : "Initial state of proof automaton must be labeled 'true'";
		}

		for (final var accepting : proof.getFinalStates()) {
			assert "false".equals(
					accepting.getFormula().toString()) : "Accepting state of proof automaton must be labeled 'false'";
			assert NestedWordAutomataUtils.isSinkState(proof, accepting) : "State 'false' should be a sink";
		}

		assert new InductivityCheck<>(mServices, proof, false, true, mHtc).getResult();
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
		final var syntax = "(forall (" + varDescr + ") true)";
		final var formula = (QuantifiedFormula) TermParseUtils.parseTerm(mMgdScript.getScript(), syntax);

		for (final var quantVar : formula.getVariables()) {
			final var pv = ProgramVarUtils.constructGlobalProgramVarPair(quantVar.getName(), quantVar.getSort(),
					mMgdScript, null);
			symbolTable.add(pv);
		}

		return symbolTable;
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
		final Pattern actionPattern = Pattern.compile("\\s*\\[(\\d+)\\]\\s+\\{([^\\}]*)\\}\\s+([^\\s].*)$");
		for (final var actionLine : actionLines) {
			final String actionDescr = actionLine.substring(prefix.length());
			final var matcher = actionPattern.matcher(actionDescr);
			assert matcher.find();

			final int id = Integer.parseUnsignedInt(matcher.group(1));
			final var assignedVarNames = Arrays.stream(matcher.group(2).split(",")).map(String::trim)
					.filter(s -> !s.isEmpty()).collect(Collectors.toSet());
			final var assignedVars = mSymbolTable.getGlobals().stream()
					.filter(pv -> assignedVarNames.contains(pv.getIdentifier())).collect(Collectors.toSet());
			final String transformulaString = matcher.group(3);

			if (result.containsKey(id)) {
				throw new IllegalArgumentException("duplicate definition for action [" + id + "]");
			}

			final var action = new SimpleAction(id, parseTransformula(transformulaString, assignedVars));
			result.put(id, action);
		}

		return result;
	}

	private UnmodifiableTransFormula parseTransformula(final String syntax, final Set<IProgramNonOldVar> assignedVars) {
		final var term = SmtParserUtils.parseWithVariables(syntax, mServices, mMgdScript, mSymbolTable);

		final var inVars = mSymbolTable.getGlobals().stream()
				.collect(Collectors.toMap(IProgramVar.class::cast, pv -> getOldTermVariable(pv, assignedVars)));
		final var outVars = mSymbolTable.getGlobals().stream()
				.collect(Collectors.toMap(IProgramVar.class::cast, IProgramVar::getTermVariable));
		final var builder = new TransFormulaBuilder(inVars, outVars, true, null, true, null, true);
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

		// parse states
		final var stateMap = new HashMap<String, IPredicate>();
		for (final var state : aut.getStates()) {
			final var parsedState = parsePredicate(state);
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

	private IPredicate parsePredicate(final String state) {
		final Term term = SmtParserUtils.parseWithVariables(state, mServices, mMgdScript, mSymbolTable);
		return mUnifier.getOrConstructPredicate(term);
	}

	private static SimpleAction parseAction(final Map<Integer, SimpleAction> id2Action, final String label) {
		final var pattern = Pattern.compile("^\\[(\\d+)\\]$");
		final var matcher = pattern.matcher(label);
		assert matcher.find();

		final int id = Integer.parseUnsignedInt(matcher.group(1));
		if (!id2Action.containsKey(id)) {
			throw new IllegalArgumentException("Undefined action [" + id + "]");
		}
		return id2Action.get(id);
	}

	@Override
	public void printMessage(final Severity severityForResult, final LoggerSeverity severityForLogger,
			final String longDescr, final String shortDescr, final AtsASTNode node) {
		// TODO
		mLogger.warn(longDescr);
	}

	private final class OwickiGriesTestCase implements Comparable<OwickiGriesTestCase> {
		private final Path mPath;

		public OwickiGriesTestCase(final Path path) {
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
		public int compareTo(final OwickiGriesTestCase other) {
			return mPath.compareTo(other.mPath);
		}
	}

	private static final class SimpleAction implements IInternalAction {
		private static final String PROCEDURE = "Main";

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
