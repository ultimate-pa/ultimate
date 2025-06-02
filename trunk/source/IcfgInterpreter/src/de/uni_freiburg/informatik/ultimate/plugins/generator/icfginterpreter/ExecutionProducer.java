package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramExecutions.ExecutionTermintionReason;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.Restriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.ArrayValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.EqualityExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.EqualityExtractor.EdgeUntranslatableError;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.EqualityExtractor.Equations;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Equation.SolvedEquation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.InterpretedIcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.InterpretedIcfgEdge.InterpretedIcfgEdgeBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.InterpretedIcfgEdge.UntranslatableIcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.TermEvaluator.UnsopportedTermError;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Update;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Update.AssignmentUpdate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Update.HavocUpdate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Value;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences.IcfgInterpreterPreferences;

public class ExecutionProducer {
	private final HashMap<String, Set<IcfgLocation>> mErrorMap;
	private final HashMap<IcfgLocation, ArrayList<InterpretedIcfgEdge>> mOutEdges = new HashMap<>();
	private final ManagedScript mngScript;
	private final HashMap<TermVariable, IProgramVar> mSymbolTable = new HashMap<>();
	private int unfinishedMaxStored = 1024;
	private final IIcfg<? extends IcfgLocation> mIcfg;
	private int executionMaxLength;
	private int variantsPerHavoc;

	public ExecutionProducer(final IIcfg<? extends IcfgLocation> icfg, final IUltimateServiceProvider services) {
		mIcfg = icfg;

		final Set<? extends IcfgLocation> initialNodes = mIcfg.getInitialNodes();
		mngScript = mIcfg.getCfgSmtToolkit().getManagedScript();

		final Script script = mngScript.getScript();

		final HashSet<IcfgLocation> visited = new HashSet<>();
		final ArrayList<IcfgLocation> next = new ArrayList<>(initialNodes);

		while (next.size() > 0) {
			final IcfgLocation source = next.remove(0);

			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				final IcfgLocation target = edge.getTarget();

				if (!visited.contains(target)) {
					next.add(target);
					visited.add(target);
				}

				final UnmodifiableTransFormula formula = edge.getTransformula();

				System.out.println(formula.toStringDirect());
				printDNF(formula.getFormula(), 0, services);

				for (final Entry<IProgramVar, TermVariable> programVar : formula.getInVars().entrySet()) {
					mSymbolTable.put(programVar.getValue(), programVar.getKey());
				}
				for (final Entry<IProgramVar, TermVariable> programVar : formula.getOutVars().entrySet()) {
					mSymbolTable.put(programVar.getValue(), programVar.getKey());
				}
				for (final Entry<IProgramVar, TermVariable> programVar : formula.getOutVars().entrySet()) {
					mSymbolTable.put(programVar.getValue(), programVar.getKey());
				}

				final ArrayList<InterpretedIcfgEdge> allOutEdges = mOutEdges.getOrDefault(source, new ArrayList<>());
				allOutEdges.addAll(extractEdges(formula, edge, script, services));
				mOutEdges.put(source, allOutEdges);
			}
		}

		mErrorMap = getErrorLocations(mIcfg);
	}

	public Map<ExecutionTermintionReason, List<IcfgProgramExecution<IcfgEdge>>> makeExecutions(final ILogger logger)
			throws Exception {

		IcfgInterpreterPreferences.updatePreferences();

		final int seed = IcfgInterpreterPreferences.getPreferences()
				.getInt(IcfgInterpreterPreferences.SettingLabel.EXECUTION_SEED.toString());

		final int testExecutionCount = Math.max(1, IcfgInterpreterPreferences.getPreferences()
				.getInt(IcfgInterpreterPreferences.SettingLabel.EXECUTIONS_PER_ENTRYPOINT.toString()));

		variantsPerHavoc = Math.max(1, IcfgInterpreterPreferences.getPreferences()
				.getInt(IcfgInterpreterPreferences.SettingLabel.VARIANTS_PER_HAVOC_EDGE.toString()));

		unfinishedMaxStored = Math.max(1, IcfgInterpreterPreferences.getPreferences()
				.getInt(IcfgInterpreterPreferences.SettingLabel.EXECUTIONS_QUEUED.toString()));

		executionMaxLength = Math.max(0, IcfgInterpreterPreferences.getPreferences()
				.getInt(IcfgInterpreterPreferences.SettingLabel.EXECUTION_MAX_LENGTH.toString()));

		final int bitsHavoced = Math.max(4, IcfgInterpreterPreferences.getPreferences()
				.getInt(IcfgInterpreterPreferences.SettingLabel.BITS_HAVOCED.toString()));

		logger.info("Creating " + testExecutionCount + " executions per initial node.");

		final Set<? extends IcfgLocation> initialNodes = mIcfg.getInitialNodes();

		final NonDeterministicChoice ndc = new NonDeterministicChoice(seed, bitsHavoced);

		final Map<ExecutionTermintionReason, List<IcfgProgramExecution<IcfgEdge>>> executions = new HashMap<>();

		final long startTime = System.nanoTime();
		for (final IcfgLocation node : initialNodes) {
			for (int i = 0; i < testExecutionCount; i++) {
				final Map<ExecutionTermintionReason, List<IcfgProgramExecution<IcfgEdge>>> newExecutions = makeExecutions(
						ndc, node);
				for (final ExecutionTermintionReason reason : newExecutions.keySet()) {
					// executions.getOrDefault(executions, null)
					final List<IcfgProgramExecution<IcfgEdge>> executionList = executions.getOrDefault(reason,
							new ArrayList<>());
					executionList.addAll(newExecutions.get(reason));
					executions.put(reason, executionList);
				}
			}
		}
		final long endTime = System.nanoTime();

		final long executionTime = endTime - startTime;

		logger.info(getClass().getSimpleName() + " used " + (executionTime / 1000000.0) + "ms for execution.");
		return executions;
	}

	private static <LOC extends IcfgLocation> HashMap<String, Set<IcfgLocation>> getErrorLocations(
			final IIcfg<LOC> icfg) {
		final HashMap<String, Set<IcfgLocation>> out = new HashMap<>();

		for (final Entry<String, Set<LOC>> entry : icfg.getProcedureErrorNodes().entrySet()) {
			out.put(entry.getKey(), new HashSet<>(entry.getValue()));
		}
		return out;
	}

	public List<InterpretedIcfgEdge> extractEdges(final UnmodifiableTransFormula formula, final IcfgEdge edge,
			final Script script, final IUltimateServiceProvider services) {
		// check if this transition is only a guard
		final List<TermVariable> outVars = formula.getOutVars().entrySet().stream()
				.filter((entry) -> formula.getAssignedVars().contains(entry.getKey())).map((entry) -> entry.getValue())
				.toList();

		final Set<TermVariable> auxVars = formula.getAuxVars();

		if (!Arrays.asList(formula.getFormula().getFreeVars()).stream().anyMatch((var) -> outVars.contains(var))) {
			// This term contains no information that is needed in updates or all updates are havocs.
			// (The formula contains no OutVar that is assigned)

			try {
				final InterpretedIcfgEdge icfgEdge = new InterpretedIcfgEdgeBuilder(edge, auxVars)
						.addUpdates(extractUpdates(formula, script, script.getTheory().mTrue))
						.makeGuardUnchanged(services, mngScript, formula).finish();

				// make sure that the extracted guard is equivalent to the whole transition formula
				final Term fullTermSub = substituteProgramVars(formula.getFormula(), formula);
				assert SmtUtils.checkEquivalence(icfgEdge.getGuardTerm(), fullTermSub, script) == LBool.UNSAT;

				System.out.println(icfgEdge.toString());
				System.out.println("\n\n");
				return List.of(icfgEdge);
			} catch (final EdgeUntranslatableError untranslated) {
				return List.of(new UntranslatableIcfgEdge(edge));
			}
		}

		if (formula.getFormula() instanceof final ApplicationTerm app
				&& app.getFunction().getName().equals(SMTLIBConstants.OR)) {
			// check if we have two opposite assignments like:
			// ((var x = true && guardA) || (var y = false && guardB))
			final Term[] subTerms = app.getParameters();
			if (subTerms.length != 2) {
				return List.of();
			}

			final InterpretedIcfgEdge icfgEdgeA = new InterpretedIcfgEdgeBuilder(edge, auxVars)
					.addUpdates(extractUpdates(formula, script, subTerms[0]))
					.makeGuardFromTerm(services, mngScript, formula, subTerms[0]).finish();

			final InterpretedIcfgEdge icfgEdgeB = new InterpretedIcfgEdgeBuilder(edge, auxVars)
					.addUpdates(extractUpdates(formula, script, subTerms[1]))
					.makeGuardFromTerm(services, mngScript, formula, subTerms[1]).finish();

			final Term notGuardB = SmtUtils.not(script, icfgEdgeB.getGuardTerm());
			if (SmtUtils.checkEquivalence(icfgEdgeA.getGuardTerm(), notGuardB, script) != LBool.UNSAT) {
				// the two have guards that are not opposites

				IcfgInterpreterObserver.getLogger()
						.error("This plug-in does not handle or terms that encode different paths of a program.\n"
								+ "Try using SingleStatement in your Icfg / Cfg Builder settings\nOffending Term:\n"
								+ app.toStringDirect() + "\nof Transition\n" + formula.toStringDirect());
				return List.of(new UntranslatableIcfgEdge(edge));
			}

			final Term notUpdatesB = SmtUtils.not(script, icfgEdgeB.getUpdateTerm(script));
			if (SmtUtils.checkEquivalence(icfgEdgeA.getUpdateTerm(script), notUpdatesB, script) != LBool.UNSAT) {
				// the two have updates that are not opposites
				IcfgInterpreterObserver.getLogger()
						.error("This plug-in does not handle or terms that encode different paths of a program.\n"
								+ "Try using SingleStatement in your Icfg / Cfg Builder settings\nOffending Term:\n"
								+ app.toStringDirect() + "\nof Transition\n" + formula.toStringDirect());
				return List.of(new UntranslatableIcfgEdge(edge));
			}

			System.out.println(icfgEdgeA.toString());
			System.out.println(icfgEdgeB.toString());
			System.out.println("\n\n");
			return List.of(icfgEdgeA, icfgEdgeB);
		}

		try {
			final InterpretedIcfgEdge icfgEdge = new InterpretedIcfgEdgeBuilder(edge, auxVars)
					.addUpdates(extractUpdates(formula, script, formula.getFormula()))
					.makeGuardUnchanged(services, mngScript, formula).finish();

			System.out.println(icfgEdge.toString());
			System.out.println("\n\n");
			return List.of(icfgEdge);

		} catch (final EdgeUntranslatableError untranslated) {
			return List.of(new UntranslatableIcfgEdge(edge));
		}
	}

	private Update[] extractUpdates(final UnmodifiableTransFormula formula, final Script script, final Term term) {
		final Equations equations = EqualityExtractor.extract(term, script, formula);
		final Set<SolvedEquation> solvedEquations = equations.solveForAllVars(script);
		return makeUpdates(solvedEquations, formula);
	}

	private Update[] makeUpdates(final Set<SolvedEquation> equations, final UnmodifiableTransFormula formula) {
		// Equations have to be ordered such that
		// 1. A variable that is defined by a last state value comes before any update that overrides the required
		// update
		// Unordered, relies on this vs. next state (a vs a'):
		// c' = b' + a; b' = 2 * a; a' = a mod 5
		// Correct order (only has one version of a variable):
		// b := 2 * a; c := b + a; a := a mod 5

		// TODO what if b' = 2 * a; a' = a mod b;

		final HashSet<TermVariable> assignableVars = new HashSet<>(formula.getAuxVars());
		assignableVars.addAll(formula.getOutVars().values().stream().filter((outVar) -> {
			return !formula.getInVars().containsValue(outVar);
		}).toList());

		final ArrayList<SolvedEquation> equationList = new ArrayList<>(equations.stream().filter((eq) -> {
			return assignableVars.contains(eq.getLhs());
		}).toList());

		// For each equation, the set of InVars / OutVars that are used. They need to come before / after all
		// equations that define these variables.
		final HashMap<SolvedEquation, List<TermVariable>> neededInVars = new HashMap<>();
		final HashMap<SolvedEquation, List<TermVariable>> neededOutVars = new HashMap<>();

		final Map<IProgramVar, TermVariable> formulaInVars = formula.getInVars();
		final Map<IProgramVar, TermVariable> formulaOutVars = formula.getOutVars();
		final Set<TermVariable> formulaAuxVars = formula.getAuxVars();

		for (final SolvedEquation equation : equationList) {
			final List<TermVariable> inVars = neededInVars.getOrDefault(equation, new ArrayList<>());
			final List<TermVariable> outVars = neededOutVars.getOrDefault(equation, new ArrayList<>());
			for (final TermVariable usedVar : equation.getRhs().getFreeVars()) {
				if (formulaInVars.containsValue(usedVar) && formulaOutVars.containsValue(usedVar)) {
					// The variable does not change, the value is the same in both states, doesn't affect order
					continue;
				}
				if (formulaInVars.containsValue(usedVar)) {
					inVars.add(lookupSymbolTableSafe(usedVar, formula));
				}
				if (formulaOutVars.containsValue(usedVar) || formulaAuxVars.contains(usedVar)) {
					outVars.add(lookupSymbolTableSafe(usedVar, formula));
				}
			}
			neededInVars.put(equation, inVars);
			neededOutVars.put(equation, outVars);
		}

		for (final Entry<IProgramVar, TermVariable> inVar : formula.getInVars().entrySet()) {
			// A variable is freely havoced if it has an InVar but no OutVar
			if (formula.getOutVars().containsKey(inVar.getKey())) {
				continue;
			}
			final SolvedEquation havocEquation = new SolvedEquation(null, inVar.getValue(), null);
			equationList.add(havocEquation);
			neededInVars.put(havocEquation, new ArrayList<>());
			neededOutVars.put(havocEquation, new ArrayList<>());
		}

		for (final Entry<IProgramVar, TermVariable> outVar : formula.getOutVars().entrySet()) {
			// A variable is freely havoced if it has an OutVar but isn't defined in the transition and not an InVar
			if (formula.getInVars().containsKey(outVar.getKey())
					|| equationList.stream().anyMatch(equation -> equation.getLhs().equals(outVar.getValue()))) {
				continue;
			}
			final SolvedEquation havocEquation = new SolvedEquation(null, outVar.getValue(), null);
			equationList.add(havocEquation);
			neededInVars.put(havocEquation, new ArrayList<>());
			neededOutVars.put(havocEquation, new ArrayList<>());
		}

		for (final TermVariable outVar : formula.getAuxVars()) {
			// An aux variable is freely havoced if it isn't defined in the transition
			if (equationList.stream().anyMatch(equation -> equation.getLhs().equals(outVar))) {
				continue;
			}
			final SolvedEquation havocEquation = new SolvedEquation(null, outVar, null);
			equationList.add(havocEquation);
			neededInVars.put(havocEquation, new ArrayList<>());
			neededOutVars.put(havocEquation, new ArrayList<>());
		}

		Collections.sort(equationList, (eq1, eq2) -> {
			final TermVariable var1 = lookupSymbolTableSafe(eq1.getLhs(), formula);
			final TermVariable var2 = lookupSymbolTableSafe(eq2.getLhs(), formula);
			if (neededInVars.get(eq1).contains(var2)) {
				// Equation 1 uses the variable defined by equation 2 in the last state context.
				// Equation 1 comes first.
				return -1;
			}
			if (neededOutVars.get(eq1).contains(var2)) {
				// Equation 1 uses the variable defined by equation 2 in the next state context.
				// Equation 2 comes first.
				return 1;
			}
			if (neededInVars.get(eq2).contains(var1)) {
				// Equation 2 uses the variable defined by equation 1 in the last state context.
				// Equation 2 comes first.
				return 1;
			}
			if (neededOutVars.get(eq2).contains(var1)) {
				// Equation 2 uses the variable defined by equation 1 in the next state context.
				// Equation 1 comes first.
				return -1;
			}
			// Otherwise, sort by name for consistent ordering of terms
			return Integer.compare(var1.getName().hashCode(), var2.getName().hashCode());
		});

		final ArrayList<Update> out = new ArrayList<>();

		while (!equationList.isEmpty()) {
			final SolvedEquation equation = equationList.get(0);
			TermVariable definedVar = equation.getLhs();

			final List<SolvedEquation> definitions = equationList.stream()
					.filter((eq) -> eq.getLhs().equals(equation.getLhs())).toList();

			// Remove all equations that define this variable
			equationList.removeAll(definitions);

			if (equation.getRhs() == null || equation.getRelation() == null) {
				// can be havoced to any value
				out.add(new HavocUpdate(lookupSymbolTableSafe(definedVar, formula), new ArrayList<>()));
				continue;
			}

			final ArrayList<SolvedEquation> equals = new ArrayList<>();
			final ArrayList<SolvedEquation> inequals = new ArrayList<>();

			for (final SolvedEquation definition : definitions) {
				if (definition.getRelation().equals(RelationSymbol.EQ)) {
					equals.add(generalize(definition, formula));
					break;
				}
				inequals.add(generalize(definition, formula));
			}

			// Replace the formula specific TermVariable with its generic global counterpart
			definedVar = lookupSymbolTableSafe(definedVar, formula);

			if (!equals.isEmpty()) {
				// We have at least one Term that directly defines the variable.
				out.add(new AssignmentUpdate(definedVar, substituteProgramVars(equals.get(0).getRhs(), formula)));
			} else {
				// We only have bounds for the Term.
				out.add(new HavocUpdate(definedVar, inequals));
			}
		}

		return out.toArray(new Update[out.size()]);
	}

	private TermVariable lookupSymbolTableSafe(final TermVariable var, final UnmodifiableTransFormula formula) {
		if (formula.getAuxVars().contains(var)) {
			return var;
		}
		return mSymbolTable.get(var).getTermVariable();
	}

	private SolvedEquation generalize(final SolvedEquation equation, final UnmodifiableTransFormula formula) {
		final TermVariable genericVar = lookupSymbolTableSafe(equation.getLhs(), formula);
		final Term genericTerm = substituteProgramVars(equation.getRhs(), formula);
		return new SolvedEquation(equation.getRelation(), genericVar, genericTerm);
	}

	private Term substituteProgramVars(final Term term, final UnmodifiableTransFormula formula) {
		final HashSet<Entry<IProgramVar, TermVariable>> vars = new HashSet<>(formula.getInVars().entrySet());
		vars.addAll(formula.getOutVars().entrySet());
		final var subst = vars.stream().collect(Collectors.toMap(e -> e.getValue(), e -> e.getKey().getTermVariable()));

		return Substitution.apply(mngScript, subst, term);
	}

	private void printDNF(final Term term, final int depth, final IUltimateServiceProvider service) {
		final String indent = "\t".repeat(depth);
		switch (term) {
		case final ApplicationTerm at:
			if (at.getFunction().getName().equals(SMTLIBConstants.OR)) {
				System.out.println(indent + "(or");
				for (final Term subTerm : at.getParameters()) {
					printDNF(subTerm, depth + 1, service);
				}
				System.out.println(indent + ")");
			} else if (at.getFunction().getName().equals(SMTLIBConstants.AND)) {
				System.out.println(indent + "(and");
				for (final Term subTerm : at.getParameters()) {
					printDNF(subTerm, depth + 1, service);
				}
				System.out.println(indent + ")");
			} else {
				System.out.println(indent + term.toStringDirect());
			}
			break;
		default:
			System.out.println(indent + term.toStringDirect());
		}
	}

	private HashMap<Term, Value> makeState(final NonDeterministicChoice ndc) {
		final HashMap<Term, Value> state = new HashMap<>();

		for (final IProgramVar programVar : mSymbolTable.values()) {
			final TermVariable termVar = programVar.getTermVariable();
			if (state.containsKey(termVar)) {
				continue;
			}
			switch (programVar.getSort().getName()) {
			case SMTLIBConstants.ARRAY:
				state.put(termVar, ndc.newArray(programVar.getSort()));
				break;
			case SMTLIBConstants.BITVEC:
				final int length = Util.getBitVecLength(programVar.getSort());
				state.put(termVar, ndc.havocBitVector(length, null));
				break;
			case SMTLIBConstants.BOOL:
				state.put(termVar, ndc.havocBool(null));
				break;
			case SMTLIBConstants.INT:
				state.put(termVar, ndc.havocInt(null));
				break;
			}
		}
		return state;
	}

	private Map<Term, Term> castMap(final Map<Term, Value> state) {
		final HashMap<Term, Term> out = new HashMap<>();

		for (final Entry<Term, Value> entry : state.entrySet()) {
			switch (entry.getValue()) {
			case final ArrayValue av:
				out.putAll(av.makeOutValues(mngScript.getScript(), entry.getKey()));
				break;
			default:
				out.put(entry.getKey(), entry.getValue().toTerm(mngScript.getScript()));
				break;
			}
		}

		return out;
	}

	public Map<ExecutionTermintionReason, List<IcfgProgramExecution<IcfgEdge>>> makeExecutions(
			final NonDeterministicChoice ndc, final IcfgLocation source) {
		final HashMap<Term, Value> state = makeState(ndc);

		final ArrayDeque<PartialExecution> executions = new ArrayDeque<>();
		executions.add(new PartialExecution(source, ndc, List.of(), List.of(state), new HashMap<>(), null));

		final Map<ExecutionTermintionReason, List<IcfgProgramExecution<IcfgEdge>>> out = new HashMap<>();

		while (!executions.isEmpty()) {
			final PartialExecution execution = executions.pop();

			if (executionMaxLength != 0 && execution.edges.size() >= executionMaxLength) {
				printExecution(execution.finish(ExecutionTermintionReason.EXECUTION_TOO_LONG), out);
				continue;
			}

			final Map<Term, Value> stateReference = execution.getCurrentState();
			final List<InterpretedIcfgEdge> nextEdges = mOutEdges.getOrDefault(execution.currentLocation,
					new ArrayList<>());

			final IcfgLocation currentLocation = execution.currentLocation;
			if (mErrorMap.getOrDefault(currentLocation.getProcedure(), new HashSet<>()).contains(currentLocation)) {
				printExecution(execution.finish(ExecutionTermintionReason.REACHED_ERROR), out);
				continue;
			}

			if (nextEdges.size() == 0) {
				// No edges exist from the current vertex
				printExecution(execution.finish(ExecutionTermintionReason.REACHED_EXIT), out);
				continue;
			}

			final List<InterpretedIcfgEdge> availableEdges = new ArrayList<>();

			boolean unsupportedFound = false;

			for (final InterpretedIcfgEdge nextEdge : nextEdges) {
				try {
					if (nextEdge.guard(stateReference, execution.ndc, execution.havocBounds)) {
						availableEdges.add(nextEdge);
					}
				} catch (final UnsopportedTermError | EdgeUntranslatableError unsupported) {
					unsupportedFound = true;
					final PartialExecution failedExecution = execution.addStep(nextEdge.getEdge(), new HashMap<>());
					printExecution(failedExecution.finish(ExecutionTermintionReason.REACHED_UNSUPPORTED), out);
				}
			}

			// No guard was true
			if ((availableEdges.size() == 0) && !unsupportedFound) {
				// There were no edges that failed due to not being implemented
				printExecution(execution.finish(ExecutionTermintionReason.REACHED_EXIT), out);
			}

			for (final InterpretedIcfgEdge nextEdge : availableEdges) {
				if (executions.size() >= unfinishedMaxStored) {
					// Only add new execution if there is space in the queue
					break;
				}

				final int nextExecutions = nextEdge.hasHavoc() ? variantsPerHavoc : 1;

				for (int i = 0; i < nextExecutions; i++) {
					if (executions.size() >= unfinishedMaxStored) {
						// Only add new execution if there is space in the queue
						break;
					}

					try {
						final Map<Term, Value> nextState = nextEdge.update(stateReference, ndc, execution.havocBounds);
						executions.addLast(execution.addStep(nextEdge.getEdge(), nextState));
					} catch (final UnsopportedTermError | EdgeUntranslatableError unsupported) {
						final PartialExecution failedExecution = execution.addStep(nextEdge.getEdge(), new HashMap<>());
						printExecution(failedExecution.finish(ExecutionTermintionReason.REACHED_UNSUPPORTED), out);
					}

				}
			}
		}

		return out;
	}

	private void printExecution(final PartialExecution execution,
			final Map<ExecutionTermintionReason, List<IcfgProgramExecution<IcfgEdge>>> outMap) {
		// Execution must be finished
		assert execution.status != null;
		// Report if the exit location was an error location
		if (execution.status == ExecutionTermintionReason.REACHED_ERROR) {
			IcfgInterpreterObserver.getLogger()
					.error("Execution successfully ended at error location " + execution.currentLocation.toString());
		}

		final List<Map<Term, Term>> statesCast = execution.states.stream().map(stateUncast -> castMap(stateUncast))
				.toList();

		final IcfgProgramExecution<IcfgEdge> out = createExecution(execution.edges, statesCast);

		final List<IcfgProgramExecution<IcfgEdge>> executions = outMap.getOrDefault(execution.status,
				new ArrayList<>());
		executions.add(out);
		outMap.put(execution.status, executions);
	}

	private record PartialExecution(IcfgLocation currentLocation, NonDeterministicChoice ndc, List<IcfgEdge> edges,
			List<Map<Term, Value>> states, Map<Term, Restriction<?>> havocBounds, ExecutionTermintionReason status) {
		public Map<Term, Value> getCurrentState() {
			return states.getLast();
		}

		public PartialExecution finish(final ExecutionTermintionReason reason) {
			return new PartialExecution(currentLocation, ndc, edges, states, havocBounds, reason);
		}

		public PartialExecution addStep(final IcfgEdge nextEdge, final Map<Term, Value> nextState) {
			if (status != null) {
				throw new AssertionError("Cannot add steps to finished Execution.");
			}
			final List<IcfgEdge> newEdges = new ArrayList<>(edges());
			newEdges.add(nextEdge);
			final List<Map<Term, Value>> newStates = new ArrayList<>(states());

			// TODO Propagate back havoced variables (does not yet support havoced array entries)
			int index = newStates.size() - 1;
			Map<Term, Value> previousState = newStates.get(index);
			final Set<Term> currentVars = new HashSet<>(nextState.keySet());
			while (!previousState.keySet().containsAll(currentVars)) {
				for (final Term variable : currentVars) {
					if (!previousState.containsKey(variable)) {
						previousState.put(variable, nextState.get(variable));
					} else {
						currentVars.remove(variable);
					}
				}

				index--;
				if (index < 0) {
					break;
				}
				previousState = newStates.get(index);
			}

			newStates.add(nextState);
			return new PartialExecution(nextEdge.getTarget(), ndc, newEdges, newStates, new HashMap<>(havocBounds),
					status);
		}
	}

	private static IcfgProgramExecution<IcfgEdge> createExecution(final List<IcfgEdge> trace,
			final List<Map<Term, Term>> states) {
		if (trace.isEmpty()) {
			return IcfgProgramExecution.create(IcfgEdge.class);
		}
		final Map<Integer, ProgramState<Term>> stateMapping = new HashMap<>();
		for (int i = 0; i < states.size(); i++) {
			stateMapping
					.put(i - 1,
							new ProgramState<>(
									states.get(i).entrySet().stream()
											.collect(Collectors.toMap(x -> x.getKey(), x -> List.of(x.getValue()))),
									Term.class));
		}
		return IcfgProgramExecution.create(trace, stateMapping);
	}
}
