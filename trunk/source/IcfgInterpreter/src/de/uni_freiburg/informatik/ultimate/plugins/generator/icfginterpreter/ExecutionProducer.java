package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramExecutions.ExecutionTermintionReason;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramExecutions.Pair;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.Restriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.ArrayValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.EqualityExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.EqualityExtractor.EdgeUntranslatableError;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.EqualityExtractor.Equations;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Equation.SolvedEquation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.InterpretedIcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.InterpretedIcfgEdge.InterpretedIcfgEdgeBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.InterpretedIcfgEdge.UntranslatableIcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.TermEvaluator.UnsupportedTermError;
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
	private final IIcfg<? extends IcfgLocation> mIcfg;
	private int executionMaxLength;
	private int variantsPerHavoc;
	private int unfinishedMaxStored;
	private int batchSize;
	private final Set<IcfgLocation> mErrorLocations;
	private boolean deleteBatch;
	private boolean endIfAggregateFull;
	private final IUltimateServiceProvider mServices;

	public ExecutionProducer(final IIcfg<? extends IcfgLocation> icfg, final IUltimateServiceProvider services,
			final Set<IcfgLocation> errorLocations) {
		mIcfg = icfg;
		mServices = services;

		final Set<? extends IcfgLocation> initialNodes = mIcfg.getInitialNodes();
		mngScript = mIcfg.getCfgSmtToolkit().getManagedScript();

		final Script script = mngScript.getScript();

		final HashSet<IcfgLocation> visited = new HashSet<>();
		final ArrayList<IcfgLocation> next = new ArrayList<>(initialNodes);

		while (next.size() > 0) {
			final IcfgLocation source = next.remove(0);
			final ArrayList<InterpretedIcfgEdge> allOutEdges = new ArrayList<>();
			mOutEdges.put(source, allOutEdges);

			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				if (!(edge instanceof IIcfgInternalTransition)) {
					IcfgInterpreterObserver.getLogger()
							.error("This plug-in does not handle Call or Return statements.\n"
									+ "Inline methods or avoid using them.");
					allOutEdges.add(new UntranslatableIcfgEdge(edge));
					continue;
				}

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

				allOutEdges.addAll(extractEdges(formula, edge, script, services));
			}
		}

		mErrorMap = getErrorLocations(mIcfg);
		mErrorLocations = errorLocations;
	}

	public Map<ExecutionTermintionReason, List<IcfgProgramExecution<IcfgEdge>>> makeExecutions(final ILogger logger,
			final BiConsumer<Map<ExecutionTermintionReason, List<IcfgProgramExecution<IcfgEdge>>>, Set<IcfgLocation>> outMethod)
			throws Exception {

		batchSize = IcfgInterpreterPreferences.getPreferences()
				.getInt(IcfgInterpreterPreferences.SettingLabel.PARTIAL_RESULTS_COUNT.toString());

		deleteBatch = IcfgInterpreterPreferences.getPreferences()
				.getBoolean(IcfgInterpreterPreferences.SettingLabel.PARTIAL_RESULTS_STORE.toString());

		endIfAggregateFull = IcfgInterpreterPreferences.getPreferences()
				.getBoolean(IcfgInterpreterPreferences.SettingLabel.STOP_AFTER_AGGREGARE_FULL.toString());

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

		final int minBits = Math.max(4, IcfgInterpreterPreferences.getPreferences()
				.getInt(IcfgInterpreterPreferences.SettingLabel.MIN_BITS.toString()));

		final int maxBits = Math.max(4, IcfgInterpreterPreferences.getPreferences()
				.getInt(IcfgInterpreterPreferences.SettingLabel.MAX_BITS.toString()));

		logger.info("Creating " + testExecutionCount + " executions per initial node.");

		final Set<? extends IcfgLocation> initialNodes = mIcfg.getInitialNodes();

		final NonDeterministicChoice ndc = new NonDeterministicChoice(seed, minBits, maxBits);

		final Map<ExecutionTermintionReason, List<IcfgProgramExecution<IcfgEdge>>> executions = new HashMap<>();

		for (final ExecutionTermintionReason reason : ExecutionTermintionReason.values()) {
			executions.put(reason, new ArrayList<>());
		}

		storedFinalizedExecutions = 0;
		final long startTime = System.nanoTime();
		for (final IcfgLocation node : initialNodes) {
			for (int i = 0; i < testExecutionCount; i++) {
				makeExecutions(ndc, node, executions, outMethod);
			}
		}

		if (batchSize > 0 && !executions.isEmpty()) {
			// There likely weren't enough executions to exactly fill a final batch
			outMethod.accept(executions, mErrorLocations);
			if (deleteBatch) {
				executions.forEach((x, list) -> list.clear());
			}
		} else if (batchSize == 0) {
			// All executions are processed together at the end
			outMethod.accept(executions, mErrorLocations);
		}

		for (final ExecutionTermintionReason reason : ExecutionTermintionReason.values()) {
			if (executions.get(reason).isEmpty()) {
				executions.remove(reason);
			}
		}

		final long endTime = System.nanoTime();

		final long executionTime = endTime - startTime;

		final int executionSeconds = (int) Math.floor((executionTime / 1000000.0) / 1000.0);
		final int executionSecRemainder = executionSeconds % 60;
		final double executionMSremainder = executionTime % 1000000000 / 1000000.0;

		final int executionMinutes = (int) Math.floor(executionSeconds / 60.0);

		logger.info(getClass().getSimpleName() + " used " + (executionMinutes > 0 ? executionMinutes + "m " : "")
				+ (executionSeconds > 0 ? executionSecRemainder + "s " : "") + (executionMSremainder)
				+ "ms for execution.");
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

				System.out.println(icfgEdge.toString());
				System.out.println("\n\n");
				return List.of(icfgEdge);
			} catch (final EdgeUntranslatableError untranslated) {
				return List.of(new UntranslatableIcfgEdge(edge));
			}
		}

		if (formula.getFormula() instanceof final ApplicationTerm app
				&& app.getFunction().getName().equals(SMTLIBConstants.OR)) {
			IcfgInterpreterObserver.getLogger()
					.error("This plug-in does not handle or terms that encode different paths of a program.\n"
							+ "Try using SingleStatement in your Icfg / Cfg Builder settings\nOffending Term:\n"
							+ app.toStringDirect() + "\nof Transition\n" + formula.toStringDirect());
			return List.of(new UntranslatableIcfgEdge(edge));
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
		final Set<SolvedEquation> solvedEquationsB = equations.solveForRelevantVars(script, formula);
		return makeUpdates(solvedEquationsB, formula);
	}

	private ArrayDeque<Update> sortEqs(final Map<TermVariable, List<TermVariable>> neededInVars,
			final Map<TermVariable, List<TermVariable>> neededOutVars, final Map<TermVariable, Update> equationList,
			final UnmodifiableTransFormula formula) {
		// add each update that needs no InVars (that are updated)
		// add updates for which all needed InVars already exist, but only if all that need it as invar are updated

		final ArrayDeque<Update> out = new ArrayDeque<>();
		final Set<TermVariable> updatedVars = new HashSet<>();

		final Map<TermVariable, Update> equationListGlobal = new HashMap<>();
		for (final Entry<TermVariable, Update> entry : equationList.entrySet()) {
			equationListGlobal.put(entry.getValue().getVariable(), entry.getValue());
		}

		final Map<TermVariable, List<TermVariable>> neededInVarsGlobal = new HashMap<>();
		for (final Entry<TermVariable, List<TermVariable>> entry : neededInVars.entrySet()) {
			neededInVarsGlobal.put(lookupSymbolTableSafe(entry.getKey(), formula), entry.getValue().stream()
					.map((final TermVariable var) -> lookupSymbolTableSafe(var, formula)).toList());
		}
		final Map<TermVariable, List<TermVariable>> neededOutVarsGlobal = new HashMap<>();
		for (final Entry<TermVariable, List<TermVariable>> entry : neededOutVars.entrySet()) {
			neededOutVarsGlobal.put(lookupSymbolTableSafe(entry.getKey(), formula), entry.getValue().stream()
					.map((final TermVariable var) -> lookupSymbolTableSafe(var, formula)).toList());
		}

		while (equationList.size() > updatedVars.size()) {
			final Set<TermVariable> neededInVarsTotal = Set.copyOf(
					neededInVarsGlobal.entrySet().stream().filter(entry -> !updatedVars.contains(entry.getKey()))
							.flatMap(entry -> entry.getValue().stream()).toList());

			// get variables that can be updated because all needed outvars are already updated
			final Stream<TermVariable> updatableVars = neededOutVarsGlobal.entrySet().stream()
					.filter(entry -> !updatedVars.contains(entry.getKey()) && updatedVars.containsAll(entry.getValue()))
					.map(entry -> entry.getKey());

			// only keep those updates that are not needed as InVars any more
			final List<TermVariable> safeUpdates = new ArrayList<>(
					updatableVars.filter(var -> !neededInVarsTotal.contains(var)).toList());

			// These are interchangeable. Sort by variable name for consistency
			safeUpdates.sort(Comparator.comparing(TermVariable::getName));
			for (final TermVariable updateVar : safeUpdates) {
				updatedVars.add(updateVar);
				out.addLast(equationListGlobal.get(updateVar));
			}
		}

		return out;
	}

	private Update[] makeUpdates(final Set<SolvedEquation> equations, final UnmodifiableTransFormula formula) {
		// TODO detect cycles

		final HashSet<TermVariable> assignableVars = new HashSet<>(formula.getAuxVars());
		assignableVars.addAll(formula.getOutVars().values().stream().filter((outVar) -> {
			return !formula.getInVars().containsValue(outVar);
		}).toList());
		final ArrayList<SolvedEquation> equationList = new ArrayList<>(
				equations.stream().filter((eq) -> assignableVars.contains(eq.getLhs())).toList());

		// TODO make havoc updates that execute "assume array[index] < value" etc
		final List<SolvedEquation> arrayEquations = equations.stream().filter(eq -> eq.isSelect()).toList();

		if (arrayEquations.size() > 0) {
			// Get equations where select is compared to a constant (select < 5), not an assigned var (select = var <==>
			// var = select)
			// List<SolvedEquation> updatingEquations = arrayEquations.stream().filter(eq ->
			// Set.of(eq.getRhs().getFreeVars()).stream().anyMatch(var -> formula.getAssignedVars())).toList();
		}

		// For each equation, the set of InVars / OutVars that are used. They need to come before / after all
		// equations that define these variables.
		final HashMap<TermVariable, List<TermVariable>> neededInVars = new HashMap<>();
		final HashMap<TermVariable, List<TermVariable>> neededOutVars = new HashMap<>();

		final Map<IProgramVar, TermVariable> formulaInVars = formula.getInVars();
		final Map<IProgramVar, TermVariable> formulaOutVars = formula.getOutVars();
		final Set<TermVariable> formulaAuxVars = formula.getAuxVars();

		for (final SolvedEquation equation : equationList) {
			final TermVariable updatedVar = (TermVariable) equation.getLhs();
			final List<TermVariable> inVars = neededInVars.getOrDefault(updatedVar, new ArrayList<>());
			final List<TermVariable> outVars = neededOutVars.getOrDefault(updatedVar, new ArrayList<>());

			for (final TermVariable usedVar : equation.getRhs().getFreeVars()) {
				// final TermVariable globalVar = lookupSymbolTableSafe(usedVar, formula);
				if (lookupSymbolTableSafe(updatedVar, formula) == lookupSymbolTableSafe(usedVar, formula)) {
					continue; // No need to define that x' may depend on x since it can't be updated before itself
				}
				if (formulaInVars.containsValue(usedVar) && formulaOutVars.containsValue(usedVar)) {
					// The variable does not change, the value is the same in both states, doesn't affect order
					continue;
				}
				if (formulaInVars.containsValue(usedVar)) {
					inVars.add(usedVar);
				}
				if (formulaOutVars.containsValue(usedVar) || formulaAuxVars.contains(usedVar)) {
					outVars.add(usedVar);
				}
			}

			neededInVars.put(updatedVar, inVars);
			neededOutVars.put(updatedVar, outVars);
		}

		for (final Entry<IProgramVar, TermVariable> inVar : formula.getInVars().entrySet()) {
			// A variable is freely havoced if it has an InVar but no OutVar
			// Arrays are not havoced.
			if (inVar.getValue().getSort().isArraySort() || formula.getOutVars().containsKey(inVar.getKey())) {
				continue;
			}

			final TermVariable localVar = inVar.getValue();

			final SolvedEquation havocEquation = new SolvedEquation(null, localVar, null);
			equationList.add(havocEquation);
			neededInVars.put(localVar, new ArrayList<>());
			neededOutVars.put(localVar, new ArrayList<>());
		}

		for (final Entry<IProgramVar, TermVariable> outVar : formula.getOutVars().entrySet()) {
			// A variable is freely havoced if it has an OutVar but isn't defined in the transition and not an InVar
			// Arrays are not havoced.
			if (outVar.getValue().getSort().isArraySort() || formula.getInVars().containsKey(outVar.getKey())
					|| equationList.stream().anyMatch(equation -> equation.getLhs().equals(outVar.getValue()))) {
				continue;
			}
			final TermVariable localVar = outVar.getValue();
			final SolvedEquation havocEquation = new SolvedEquation(null, localVar, null);
			equationList.add(havocEquation);
			neededInVars.put(localVar, new ArrayList<>());
			neededOutVars.put(localVar, new ArrayList<>());
		}

		for (final TermVariable auxVar : formula.getAuxVars()) {
			// An aux variable is freely havoced if it isn't defined in the transition
			// Arrays are not havoced.
			if (auxVar.getSort().isArraySort()
					|| equationList.stream().anyMatch(equation -> equation.getLhs().equals(auxVar))) {
				continue;
			}
			final SolvedEquation havocEquation = new SolvedEquation(null, auxVar, null);
			equationList.add(havocEquation);
			neededInVars.put(auxVar, new ArrayList<>());
			neededOutVars.put(auxVar, new ArrayList<>());
		}

		final Map<TermVariable, Update> updates = new HashMap<>();

		for (final TermVariable definedVar : Set
				.copyOf(equationList.stream().map(eq -> (TermVariable) eq.getLhs()).toList())) {
			final TermVariable globalVar = lookupSymbolTableSafe(definedVar, formula);

			final List<SolvedEquation> definitions = equationList.stream()
					.filter((eq) -> eq.getLhs().equals(definedVar))
					/* .filter((eq) -> formulaAuxVars.contains(eq.getLhs()) && ) */.toList();

			if (definitions.size() == 1 && definitions.get(0).getRelation() == null) {
				// This is freely havoced
				final boolean removePreviousRestrictions = formulaInVars.containsValue(definedVar);
				updates.put(globalVar, new HavocUpdate(lookupSymbolTableSafe(definedVar, formula), new ArrayList<>(),
						removePreviousRestrictions));
				continue;
			}

			final ArrayList<SolvedEquation> equals = new ArrayList<>();
			final ArrayList<SolvedEquation> inequals = new ArrayList<>();

			for (final SolvedEquation definition : definitions) {
				if (definition.getRelation().equals(RelationSymbol.EQ)) {
					equals.add(generalize(definition, formula));
					continue;
				}
				inequals.add(generalize(definition, formula));
			}

			Update newUpdate;
			if (!equals.isEmpty()) {
				// We have at least one Term that directly defines the variable.
				// Find the one that depends on the least variables
				SolvedEquation leastNeeded = equals.get(0);

				for (final SolvedEquation equalEQ : equals) {
					if (equalEQ.getFreeVars().size() < leastNeeded.getFreeVars().size()) {
						leastNeeded = equalEQ;
					}
				}
				newUpdate = new AssignmentUpdate(globalVar, substituteProgramVars(leastNeeded.getRhs(), formula));

				// Remove required in / out vars such that only those of the used term remain
				final Set<TermVariable> remainingVars = Set.of(leastNeeded.getRhs().getFreeVars());
				neededInVars.put(definedVar, neededInVars.get(definedVar).stream()
						.filter(var -> remainingVars.contains(lookupSymbolTableSafe(var, formula))).toList());
				neededOutVars.put(definedVar, neededOutVars.get(definedVar).stream()
						.filter(var -> remainingVars.contains(lookupSymbolTableSafe(var, formula))).toList());
			} else {
				// We only have bounds for the Term.

				// Remove previous restrictions if the variable that was havoced is havoced again (not an invar)
				// If it is an InVar, then we may have had an edge with restricted havoc, and an assume on this edge.
				final boolean removePreviousRestrictions = formulaInVars.containsValue(definedVar);
				newUpdate = new HavocUpdate(globalVar, inequals, removePreviousRestrictions);
			}

			updates.put(definedVar, newUpdate);
		}

		// TODO make restrictions from array equations
		final ArrayDeque<Update> updatesSorted = sortEqs(neededInVars, neededOutVars, updates, formula);

		return updatesSorted.toArray(new Update[updatesSorted.size()]);
	}

	private Term lookupSymbolTableSafe(final Term var, final UnmodifiableTransFormula formula) {
		if (var instanceof final TermVariable tv) {
			return lookupSymbolTableSafe(tv, formula);
		}
		return var;
	}

	private TermVariable lookupSymbolTableSafe(final TermVariable var, final UnmodifiableTransFormula formula) {
		if (formula.getAuxVars().contains(var)) {
			return var;
		}
		return mSymbolTable.get(var).getTermVariable();
	}

	private SolvedEquation generalize(final SolvedEquation equation, final UnmodifiableTransFormula formula) {
		if (equation.isSelect()) {
			final ApplicationTerm at = (ApplicationTerm) equation.getLhs();
			final Term genericTerm = substituteProgramVars(equation.getRhs(), formula);
			return new SolvedEquation(equation.getRelation(), at, genericTerm);
		}
		final TermVariable genericVar = (TermVariable) lookupSymbolTableSafe(equation.getLhs(), formula);
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

	private Map<Term, Term> castMap(final Map<TermVariable, Value> state) {
		final HashMap<Term, Term> out = new HashMap<>();

		for (final Entry<TermVariable, Value> entry : state.entrySet()) {
			out.putAll(entry.getValue().toTerm(mngScript.getScript(), entry.getKey()));
		}

		return out;
	}

	private HashMap<TermVariable, Value> makeState() {
		final HashMap<TermVariable, Value> state = new HashMap<>();

		for (final IProgramVar programVar : mSymbolTable.values()) {
			final TermVariable termVar = programVar.getTermVariable();
			if (state.containsKey(termVar)) {
				continue;
			}
			if (programVar.getSort().isArraySort()) {
				state.put(termVar, new ArrayValue(new HashMap<>(), termVar));
			}
		}
		return state;
	}

	public void makeExecutions(final NonDeterministicChoice ndc, final IcfgLocation source,
			final Map<ExecutionTermintionReason, List<IcfgProgramExecution<IcfgEdge>>> out,
			final BiConsumer<Map<ExecutionTermintionReason, List<IcfgProgramExecution<IcfgEdge>>>, Set<IcfgLocation>> outMethod) {
		// Do not create new executions if we have reached the required number
		if (endIfAggregateFull && IcfgInterpreterObserver.getInstance().isAggregateFull()) {
			return;
		}

		final ArrayDeque<PartialExecution> executions = new ArrayDeque<>();
		executions.add(new PartialExecution(source, List.of(), List.of(makeState()), new HashMap<>(), null));

		final IProgressMonitorService progmon = mServices.getProgressMonitorService();
		while (!executions.isEmpty()) {
			if (!progmon.continueProcessing()) {
				break;
			}
			final PartialExecution execution = executions.pop();
			final Map<TermVariable, Value> state = execution.getCurrentState();

			if (executionMaxLength != 0 && execution.edges.size() >= executionMaxLength) {
				if (finalizeExecution(execution.finish(ExecutionTermintionReason.EXECUTION_TOO_LONG), out, outMethod)
						&& endIfAggregateFull) {
					return;
				}
				continue;
			}

			final List<InterpretedIcfgEdge> nextEdges = mOutEdges.get(execution.currentLocation);

			final IcfgLocation currentLocation = execution.currentLocation;
			if (mErrorMap.getOrDefault(currentLocation.getProcedure(), new HashSet<>()).contains(currentLocation)) {
				if (finalizeExecution(execution.finish(ExecutionTermintionReason.REACHED_ERROR), out, outMethod)
						&& endIfAggregateFull) {
					return;
				}
				continue;
			}

			if (nextEdges.size() == 0) {
				// No edges exist from the current vertex
				if (finalizeExecution(execution.finish(ExecutionTermintionReason.REACHED_EXIT), out, outMethod)
						&& endIfAggregateFull) {
					return;
				}
				continue;
			}

			boolean unsupportedFound = false;
			boolean anyGuardTrue = false;

			final Map<InterpretedIcfgEdge, List<PartialExecution>> newExecutions = new HashMap<>();
			for (final InterpretedIcfgEdge nextEdge : nextEdges) {
				// if the update reads havoced variables, create extra executions.
				final int nextExecutions = nextEdge.containsHavoc(state) ? variantsPerHavoc : 1;

				for (int i = 0; i < nextExecutions; i++) {
					try {
						final Map<TermVariable, Value> nextState = new HashMap<>(execution.getCurrentState());
						final HashMap<Term, Restriction<?>> newBounds = new HashMap<>(execution.havocBounds);

						final Pair<Boolean, Map<TermVariable, Value>> result = nextEdge.guard(nextState, ndc,
								newBounds);
						final Map<TermVariable, Value> havocedVars = result.b();

						if (!result.a()) {
							continue;
						}
						anyGuardTrue = true;

						havocedVars.putAll(nextEdge.update(nextState, ndc, newBounds));

						List<PartialExecution> newExecutionsOfEdge = newExecutions.get(nextEdge);
						if (newExecutionsOfEdge == null) {
							newExecutionsOfEdge = new ArrayList<>();
							newExecutions.put(nextEdge, newExecutionsOfEdge);
						}
						newExecutionsOfEdge.add(execution.addStep(nextEdge, nextState, newBounds, havocedVars));
					} catch (final UnsupportedTermError | EdgeUntranslatableError unsupported) {
						unsupportedFound = true;
						final PartialExecution failedExecution = execution.addStep(nextEdge, Map.of(), Map.of(),
								Map.of());
						if (finalizeExecution(failedExecution.finish(ExecutionTermintionReason.REACHED_UNSUPPORTED),
								out, outMethod) && endIfAggregateFull) {
							return;
						}
					}
				}
			}

			if (newExecutions.size() + executions.size() <= unfinishedMaxStored) {
				for (final List<PartialExecution> edgeExecutions : newExecutions.values()) {
					executions.addAll(edgeExecutions);
				}
			} else {
				final List<InterpretedIcfgEdge> remainingEdges = new ArrayList<>(newExecutions.keySet());
				while (newExecutions.size() > 0 && executions.size() < unfinishedMaxStored) {
					final InterpretedIcfgEdge chosenEdge = ndc.chooseEdge(remainingEdges);
					final List<PartialExecution> executionList = newExecutions.get(chosenEdge);
					executions.add(executionList.remove(0));
					if (executionList.isEmpty()) {
						remainingEdges.remove(chosenEdge);
					}
				}
			}

			// no more edges can be taken, and it was not because an edge could not be translated
			if (((nextEdges.size() == 0 || !anyGuardTrue) && !unsupportedFound) && unsupportedFound) {
				if (finalizeExecution(execution.finish(ExecutionTermintionReason.REACHED_EXIT), out, outMethod)
						&& endIfAggregateFull) {
					return;
				}
			}
		}
	}

	private int storedFinalizedExecutions;

	/**
	 * Cast Execution to IcfgProgramExecution and add it to output. May process the gathered IcfgProgramExecution batch
	 * of outMap via the outMethod
	 *
	 * @param execution The execution to finalize
	 * @param outMap    Maps TerminationReason to List of found Executions
	 * @param outMethod Method with which to process a full batch
	 * @return True if the required number of executions was found
	 */
	private boolean finalizeExecution(final PartialExecution execution,
			final Map<ExecutionTermintionReason, List<IcfgProgramExecution<IcfgEdge>>> outMap,
			final BiConsumer<Map<ExecutionTermintionReason, List<IcfgProgramExecution<IcfgEdge>>>, Set<IcfgLocation>> outMethod) {
		// Execution must be finished
		assert execution.status != null;
		// Report if the exit location was an error location
		/*
		 * if (execution.status == ExecutionTermintionReason.REACHED_ERROR) { IcfgInterpreterObserver.getLogger()
		 * .error("Execution successfully ended at error location " + execution.currentLocation.toString()); }
		 */

		final List<Map<Term, Term>> statesCast = execution.states.stream().map(stateUncast -> castMap(stateUncast))
				.toList();
		final List<IcfgEdge> edgesCast = execution.edges.stream().map(intEdge -> intEdge.getEdge()).toList();

		final IcfgProgramExecution<IcfgEdge> out = createExecution(edgesCast, statesCast);

		outMap.get(execution.status).add(out);
		storedFinalizedExecutions++;

		if (batchSize > 0 && batchSize <= storedFinalizedExecutions) {
			outMethod.accept(outMap, mErrorLocations);
			storedFinalizedExecutions = 0;
			if (deleteBatch) {
				outMap.forEach((x, list) -> list.clear());
			}
			if (IcfgInterpreterObserver.getInstance().isAggregateFull()) {
				return true;
			}
		}
		return false;
	}

	private record PartialExecution(IcfgLocation currentLocation, List<InterpretedIcfgEdge> edges,
			List<Map<TermVariable, Value>> states, Map<Term, Restriction<?>> havocBounds,
			ExecutionTermintionReason status) {
		public Map<TermVariable, Value> getCurrentState() {
			return states.getLast();
		}

		public PartialExecution finish(final ExecutionTermintionReason reason) {
			return new PartialExecution(currentLocation, edges, states, havocBounds, reason);
		}

		public PartialExecution addStep(final InterpretedIcfgEdge nextEdge, final Map<TermVariable, Value> nextState,
				final Map<Term, Restriction<?>> newBounds, final Map<TermVariable, Value> havocedVars) {
			if (status != null) {
				throw new AssertionError("Cannot add steps to finished Execution.");
			}

			final List<InterpretedIcfgEdge> newEdges = new ArrayList<>(edges());
			final List<Map<TermVariable, Value>> newStates = new ArrayList<>(states());

			int index = newStates.size() - 1;

			Map<TermVariable, Value> previousState = newStates.get(index);
			final Set<TermVariable> currentVars = new HashSet<>(havocedVars.keySet());

			nextEdge.removeSafe(currentVars);

			// Propagate havoced variables backwards
			while (!currentVars.isEmpty()) {
				// Set of variables that were havoced / removed from state on the edge leading to this state
				Set<TermVariable> havocedToThisState;
				if (index > 0) {
					final InterpretedIcfgEdge edgeToPrevState = edges().get(index - 1);
					havocedToThisState = edgeToPrevState.getHavocedVars();
				} else {
					havocedToThisState = Set.of();
				}

				final Set<TermVariable> finishedVars = new HashSet<>();

				// Make a copy of the state, as changing it would otherwise affect other executions.
				// This is preferable to blindly cloning every state in the trace at every step.
				newStates.set(index, new HashMap<>(previousState));

				for (final TermVariable variable : currentVars) {
					if (previousState.containsKey(variable)) {
						// Variable was already known in this state, stop propagating it.
						finishedVars.add(variable);
						continue;
					}

					if (havocedToThisState.contains(variable)) {
						// Variable was havoced on the edge to this state, no need to propagate further
						finishedVars.add(variable);
					}
					// Variable was havoced in this state, add known value
					previousState.put(variable, havocedVars.get(variable));
				}
				currentVars.removeAll(finishedVars);

				index--;
				if (index < 0) {
					break;
				}
				previousState = newStates.get(index);
			}

			newStates.add(nextState);
			newEdges.add(nextEdge);

			return new PartialExecution(nextEdge.getTarget(), newEdges, newStates, newBounds, status);
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
