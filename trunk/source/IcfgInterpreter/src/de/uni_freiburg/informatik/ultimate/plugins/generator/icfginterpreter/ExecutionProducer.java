package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Random;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.compiled.EnumState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.compiled.IVariableName;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.compiled.JavaCodeEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.IcfgExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.IcfgTranslation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.InterpretedIcfg;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.ArrayValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.BitVecValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.BoolValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.EqualityExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.EqualityExtractor.Equations;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.EqualityExtractor.Equations.SolvedEquations;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Equation.SolvedEquation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.IntValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.InterpretedIcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.InterpretedIcfgEdge.PossibleUpdate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Update;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Update.AssignmentUpdate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Update.HavocUpdate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Value;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences.IcfgInterpreterPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences.Settings;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class ExecutionProducer {
	public interface IIcfgExecutionProducer {
		boolean printExecution = true;

		void init(InterpretedIcfg intIcfg, IUltimateServiceProvider services);

		IcfgProgramExecution<?> makeExecution(NonDeterministicChoice ndc, IcfgLocation source);
	}

	public static void makeExecutions(final IIcfg<? extends IcfgLocation> icfg, final IUltimateServiceProvider services,
			final ILogger logger, final IIcfgExecutionProducer producer, final Random random) throws Exception {
		IcfgInterpreterPreferences.updatePreferences();
		final int testExecutionCount = Math.max(1, IcfgInterpreterPreferences.getPreferences()
				.getInt(IcfgInterpreterPreferences.SettingLabel.EXECUTIONS_PER_ENTRYPOINT.toString()));

		logger.info("Creating " + testExecutionCount + " executions per initial node.");

		final Set<? extends IcfgLocation> initialNodes = icfg.getInitialNodes();
		final NonDeterministicChoice ndc = Settings.getSettings().getNDC();

		final InterpretedIcfg execIcfg = IcfgTranslation.parseIcfg(icfg, services);

		final long startTime = System.nanoTime();
		producer.init(execIcfg, services);
		final long initTime = System.nanoTime();
		for (final IcfgLocation node : initialNodes) {
			for (int i = 0; i < testExecutionCount; i++) {
				final long seed = random.nextLong();
				final NonDeterministicChoice ndcInstance = ndc.newInstance(seed);
				producer.makeExecution(ndcInstance, node);
			}
		}
		final long endTime = System.nanoTime();

		final long initTotal = initTime - startTime;
		final long executionTime = endTime - initTime;

		logger.info(
				producer.getClass().getSimpleName() + " used " + (initTotal / 1000000.0) + "ms for initialitation.");
		logger.info(producer.getClass().getSimpleName() + " used " + (executionTime / 1000000.0) + "ms for execution.");
	}

	private static <LOC extends IcfgLocation> HashMap<String, Set<IcfgLocation>> getErrorLocations(
			final IIcfg<LOC> icfg) {
		final HashMap<String, Set<IcfgLocation>> out = new HashMap<>();

		for (final Entry<String, Set<LOC>> entry : icfg.getProcedureErrorNodes().entrySet()) {
			out.put(entry.getKey(), new HashSet<>(entry.getValue()));
		}
		return out;
	}

	public static class CompiledEnumExecutionProducer<T extends Enum<T> & IVariableName>
			implements IIcfgExecutionProducer {
		private HashMap<IcfgLocation, ArrayList<JavaCodeEdge<T>>> compiledEdges;
		private Function<NonDeterministicChoice, EnumState<T>> stateMaker;
		HashSet<IcfgLocation> mErrorLocation;
		private HashMap<String, Set<IcfgLocation>> mErrorMap;

		@Override
		public void init(final InterpretedIcfg intIcfg, final IUltimateServiceProvider services) {
			final HashSet<Variable> variables = intIcfg.getVariables();
			try {
				final Class<T> enumClass = DynamicLoader.makeVariableNameEnum(variables);
				compiledEdges = (DynamicLoader.makeUpdates(intIcfg, enumClass));
				stateMaker = EnumState.getStateInitializer(variables, enumClass);
			} catch (final Exception e) {
				e.printStackTrace();
				return;
			}

			mErrorMap = getErrorLocations(intIcfg.getIcfg());
		}

		@Override
		public IcfgProgramExecution<?> makeExecution(final NonDeterministicChoice ndc, final IcfgLocation source) {
			final ArrayList<EnumState<T>> states = new ArrayList<>();
			final ArrayList<JavaCodeEdge<T>> edges = new ArrayList<>();
			EnumState<T> state = stateMaker.apply(ndc);
			states.add(state);

			ArrayList<JavaCodeEdge<T>> nextEdges = compiledEdges.getOrDefault(source, new ArrayList<>());

			while (nextEdges.size() > 0) {
				final EnumState<T> stateReference = state;
				final List<JavaCodeEdge<T>> availableEdges = nextEdges.stream().filter((edge) -> {
					return edge.guard(stateReference);
				}).toList();

				JavaCodeEdge<T> nextEdge;
				if (availableEdges.size() > 1) {
					nextEdge = ndc.chooseEdge(availableEdges);
				} else if (availableEdges.size() == 0) {
					// No guard was true, or no edges exist from the current vertex
					break;
				} else {
					nextEdge = availableEdges.get(0);
				}

				edges.add(nextEdge);
				state = nextEdge.update(state);
				states.add(state);

				nextEdges = compiledEdges.getOrDefault(nextEdge.getTarget(), new ArrayList<>());
			}

			if (printExecution) {
				final StringBuilder out = new StringBuilder();
				out.append(states.get(0).toString());
				for (int i = 0; i < edges.size(); i++) {
					out.append("\n->\n").append(edges.get(i));
					out.append("\n->\n").append(states.get(i + 1));
				}
				IcfgInterpreterObserver.getLogger().info(out.toString());
			}

			// Report if the exit location was an error location
			final IcfgLocation finalLocation = edges.get(edges.size() - 1).getTarget();
			if (mErrorMap.getOrDefault(finalLocation.getProcedure(), new HashSet<>()).contains(finalLocation)) {
				IcfgInterpreterObserver.getLogger()
						.error("Execution successfully ended at error location " + finalLocation.toString());
			}
			return null;
		}

	}

	public static class LiteralExecutionProducer implements IIcfgExecutionProducer {
		private ArrayList<Variable> mVariables;
		private InterpretedIcfg mIIcfg;
		private HashMap<String, Set<IcfgLocation>> mErrorMap;

		@Override
		public void init(final InterpretedIcfg intIcfg, final IUltimateServiceProvider services) {
			mVariables = new ArrayList<>(intIcfg.getVariables());
			mIIcfg = intIcfg;
			mErrorMap = getErrorLocations(intIcfg.getIcfg());
		}

		@Override
		public IcfgProgramExecution<?> makeExecution(final NonDeterministicChoice ndc, final IcfgLocation source) {
			ProgramState state = new ProgramState(mVariables, ndc);
			state.finalizeState();

			final IcfgExecution execution = new IcfgExecution(state, source);

			final ArrayList<ICFGExecutionEdge> nextEdges = new ArrayList<>(mIIcfg.getOutEdges(source));

			while (!nextEdges.isEmpty()) {
				final ProgramState stateRefernce = state;
				final List<ICFGExecutionEdge> availableEdges = nextEdges.stream().filter((nextEdge) -> {
					return nextEdge.canBeTaken(stateRefernce);
				}).toList();

				ICFGExecutionEdge nextEdge;
				if (availableEdges.size() > 1) {
					nextEdge = ndc.chooseEdge(availableEdges);
				} else if (availableEdges.size() == 0) {
					// No guard was true, or no edges exist from the current vertex
					break;
				} else {
					nextEdge = availableEdges.get(0);
				}

				state = nextEdge.execute(state);
				execution.addStep(state, nextEdge.mTarget, nextEdge.getTransFormula());
				nextEdges.clear();
				nextEdges.addAll(mIIcfg.getOutEdges(nextEdge.mTarget));
			}

			if (printExecution) {
				IcfgInterpreterObserver.getLogger().info(execution.toString());
			}
			// Report if the exit location was an error location
			final IcfgLocation finalLocation = execution.getFinalStep().getLocation();
			if (mErrorMap.getOrDefault(finalLocation.getProcedure(), new HashSet<>()).contains(finalLocation)) {
				IcfgInterpreterObserver.getLogger()
						.error("Execution successfully ended at error location " + finalLocation.toString());
			}
			return null;
		}

	}

	public static class LessCodeExecutionProducer implements IIcfgExecutionProducer {
		private ArrayList<Variable> mVariables;
		private HashMap<String, Set<IcfgLocation>> mErrorMap;
		private final HashMap<IcfgLocation, ArrayList<InterpretedIcfgEdge>> mOutEdges = new HashMap<>();
		private ManagedScript mngScript;
		private final HashMap<TermVariable, IProgramVar> mSymbolTable = new HashMap<>();

		@Override
		public void init(final InterpretedIcfg intIcfg, final IUltimateServiceProvider services) {
			final IIcfg<? extends IcfgLocation> icfg = intIcfg.getIcfg();

			final Set<? extends IcfgLocation> initialNodes = icfg.getInitialNodes();
			mngScript = icfg.getCfgSmtToolkit().getManagedScript();

			final Script script = mngScript.getScript();
			final Theory theory = script.getTheory();

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

					for (final Entry<IProgramVar, TermVariable> programVar : formula.getInVars().entrySet()) {
						mSymbolTable.put(programVar.getValue(), programVar.getKey());
					}
					for (final Entry<IProgramVar, TermVariable> programVar : formula.getOutVars().entrySet()) {
						mSymbolTable.put(programVar.getValue(), programVar.getKey());
					}

					final Term dnf = SmtUtils.toDnf(services, mngScript, formula.getFormula());

					final Equations dnfSet = EqualityExtractor.extract(formula.getFormula(), mngScript);
					// dnfSet.removeGuardEquations(formula);
					final SolvedEquations solvedDnfSet = dnfSet.solveForAllVars(script);

					final Set<PossibleUpdate> updateVariants = new HashSet<>();
					for (final Set<SolvedEquation> equationSet : solvedDnfSet.equations()) {
						final List<Term> guardEquations = equationSet.stream()
								.filter(equation -> formula.getInVars().values().containsAll(equation.getFreeVars()))
								.map(equation -> generalize(equation, formula).toTerm(script)).toList();
						final Term guardTerm = SmtUtils.and(script, guardEquations);
						updateVariants.add(new PossibleUpdate(guardTerm, makeUpdates(equationSet, formula)));
					}

					if (updateVariants.size() == 1) {
						// Only one possible variant means the specific guard is the same as the guard of the edge
						final PossibleUpdate update = updateVariants.iterator().next();
						updateVariants.clear();
						updateVariants.add(new PossibleUpdate(theory.mTrue, update.updates()));
					}

					final Term fullGuard = TransFormulaUtils.computeGuardTerm(services, mngScript, formula,
							printExecution);
					final InterpretedIcfgEdge icfgEdge = new InterpretedIcfgEdge(fullGuard, updateVariants, edge);

					System.out.println(formula.toStringDirect());
					printDNF(dnf, 0, services);
					System.out.println(icfgEdge.toString());
					System.out.println("\n\n");
					final ArrayList<InterpretedIcfgEdge> allOutEdges = mOutEdges.getOrDefault(source,
							new ArrayList<>());
					allOutEdges.add(icfgEdge);
					mOutEdges.put(source, allOutEdges);
				}
			}

			mVariables = new ArrayList<>(intIcfg.getVariables());

			mErrorMap = getErrorLocations(intIcfg.getIcfg());
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

			for (final SolvedEquation equation : equationList) {
				final List<TermVariable> inVars = neededInVars.getOrDefault(equation, new ArrayList<>());
				final List<TermVariable> outVars = neededOutVars.getOrDefault(equation, new ArrayList<>());
				for (final TermVariable usedVar : equation.getRhs().getFreeVars()) {
					if (formulaInVars.containsValue(usedVar) && formulaOutVars.containsValue(usedVar)) {
						// The variable does not change, the value is the same in both states, doesn't affect order
						continue;
					}
					if (formulaInVars.containsValue(usedVar)) {
						inVars.add(usedVar);
					}
					if (formulaOutVars.containsValue(usedVar)) {
						outVars.add(usedVar);
					}
				}
				neededInVars.put(equation, inVars);
				neededOutVars.put(equation, outVars);
			}

			for (final Entry<IProgramVar, TermVariable> inVar : formulaInVars.entrySet()) {
				// A variable is freely havoced if it has an InVar but no OutVar
				if (formulaOutVars.containsKey(inVar.getKey())) {
					continue;
				}
				final SolvedEquation havocEquation = new SolvedEquation(null, inVar.getValue(), null);
				equationList.add(havocEquation);
				neededInVars.put(havocEquation, new ArrayList<>());
				neededOutVars.put(havocEquation, new ArrayList<>());
			}

			for (final Entry<IProgramVar, TermVariable> outVar : formulaOutVars.entrySet()) {
				// A variable is freely havoced if it has an OutVar but isn't defined in the transition and not an InVar
				if (formulaInVars.containsKey(outVar.getKey())
						|| equationList.stream().anyMatch(equation -> equation.getLhs().equals(outVar.getValue()))) {
					continue;
				}
				final SolvedEquation havocEquation = new SolvedEquation(null, outVar.getValue(), null);
				equationList.add(havocEquation);
				neededInVars.put(havocEquation, new ArrayList<>());
				neededOutVars.put(havocEquation, new ArrayList<>());
			}

			Collections.sort(equationList, (eq1, eq2) -> {
				if (neededInVars.get(eq1).contains(eq2.getLhs())) {
					// Equation 1 uses the variable defined by equation 2 in the last state context.
					// Equation 1 comes first.
					return -1;
				}
				if (neededOutVars.get(eq1).contains(eq2.getLhs())) {
					// Equation 1 uses the variable defined by equation 2 in the next state context.
					// Equation 2 comes first.
					return 1;
				}
				if (neededInVars.get(eq2).contains(eq1.getLhs())) {
					// Equation 2 uses the variable defined by equation 1 in the last state context.
					// Equation 2 comes first.
					return 1;
				}
				if (neededOutVars.get(eq2).contains(eq1.getLhs())) {
					// Equation 2 uses the variable defined by equation 1 in the next state context.
					// Equation 1 comes first.
					return -1;
				}
				// Otherwise, sort by name for consistent ordering of terms
				return Integer.compare(eq1.getLhs().getName().hashCode(), eq2.getLhs().getName().hashCode());
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
					out.add(new HavocUpdate(mSymbolTable.get(definedVar).getTermVariable(), new ArrayList<>()));
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
				definedVar = mSymbolTable.get(definedVar).getTermVariable();

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

		private SolvedEquation generalize(final SolvedEquation equation, final UnmodifiableTransFormula formula) {
			final TermVariable genericVar = mSymbolTable.get(equation.getLhs()).getTermVariable();
			final Term genericTerm = substituteProgramVars(equation.getRhs(), formula);
			return new SolvedEquation(equation.getRelation(), genericVar, genericTerm);
		}

		private Term substituteProgramVars(final Term term, final UnmodifiableTransFormula formula) {
			final HashSet<Entry<IProgramVar, TermVariable>> vars = new HashSet<>(formula.getInVars().entrySet());
			vars.addAll(formula.getOutVars().entrySet());
			final var subst = vars.stream()
					.collect(Collectors.toMap(e -> e.getValue(), e -> e.getKey().getTermVariable()));

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

			for (final Variable variable : mVariables) {
				final IProgramVar programVar = variable.getVariableTerm().mProgramVar;
				if (programVar == null) {
					continue;
				}
				final TermVariable termVar = programVar.getTermVariable();
				if (state.containsKey(termVar)) {
					continue;
				}
				switch (programVar.getSort().getName()) {
				case SMTLIBConstants.ARRAY:
					// TODO change NDC and havoc actual Value object
					state.put(termVar,
							new ArrayValue(new HashMap<>(), programVar.getGloballyUniqueId(), programVar.getSort()));
					break;
				case SMTLIBConstants.BITVEC:
					final int length = Util.getBitVecLength(programVar.getSort());
					final BigInteger value = ndc.havocBitVector(length, null).bv2nat();
					state.put(termVar, new BitVecValue(value, length));
					break;
				case SMTLIBConstants.BOOL:
					state.put(termVar, new BoolValue(ndc.havocBool(null)));
					break;
				case SMTLIBConstants.INT:
					state.put(termVar, new IntValue(BigInteger.valueOf(ndc.havocInt(null))));
					break;
				}
			}
			return state;
		}

		private Map<Term, Term> castMap(final Map<Term, Value> state) {
			final HashMap<Term, Term> out = new HashMap<>();

			for (final Entry<Term, Value> entry : state.entrySet()) {
				out.put(entry.getKey(), entry.getValue().toTerm(mngScript.getScript()));
			}

			return out;
		}

		@Override
		public IcfgProgramExecution<?> makeExecution(final NonDeterministicChoice ndc, final IcfgLocation source) {
			HashMap<Term, Value> state = makeState(ndc);

			final ArrayList<InterpretedIcfgEdge> nextEdges = new ArrayList<>(
					mOutEdges.getOrDefault(source, new ArrayList<>()));

			final ArrayList<HashMap<Term, Value>> states = new ArrayList<>();
			final ArrayList<IcfgEdge> edges = new ArrayList<>();

			states.add(state);

			while (!nextEdges.isEmpty()) {
				final HashMap<Term, Value> stateReference = state;
				final List<InterpretedIcfgEdge> availableEdges = nextEdges.stream().filter((nextEdge) -> {
					return nextEdge.guard(stateReference, ndc);
				}).toList();

				InterpretedIcfgEdge nextEdge;
				if (availableEdges.size() > 1) {
					nextEdge = ndc.chooseEdge(availableEdges);
				} else if (availableEdges.size() == 0) {
					// No guard was true, or no edges exist from the current vertex
					break;
				} else {
					nextEdge = availableEdges.get(0);
				}

				edges.add(nextEdge.getEdge());
				state = nextEdge.update(state, ndc);
				states.add(state);

				nextEdges.clear();
				nextEdges.addAll(mOutEdges.getOrDefault(nextEdge.getTarget(), new ArrayList<>()));
			}

			if (printExecution) {
				final StringBuilder out = new StringBuilder();
				out.append(states.get(0).toString());
				for (int i = 0; i < edges.size(); i++) {
					out.append("\n->\n").append(edges.get(i).getSource()).append(" to ")
							.append(edges.get(i).getTarget());
					out.append(" ").append(edges.get(i).getTransformula().toStringDirect());
					out.append("\n->\n{");
					for (final Entry<Term, Value> entry : states.get(i + 1).entrySet()) {
						out.append("\n\t").append(entry.getKey()).append(" = ").append(entry.getValue());
					}
					out.append("\n}");

				}
				IcfgInterpreterObserver.getLogger().info(out.toString());
			}
			// Report if the exit location was an error location
			final IcfgLocation finalLocation = edges.getLast().getTarget();
			if (mErrorMap.getOrDefault(finalLocation.getProcedure(), new HashSet<>()).contains(finalLocation)) {
				IcfgInterpreterObserver.getLogger()
						.error("Execution successfully ended at error location " + finalLocation.toString());
			}

			// trace requires same number of states and edges?
			// TODO find out if it doesn't need final or initial state
			states.remove(0);

			final List<Map<Term, Term>> statesCast = states.stream().map(stateUncast -> castMap(stateUncast)).toList();

			// TODO make toTerm() for ArrayValue
			return null;// createExecution(edges, statesCast);
		}

		@SuppressWarnings("unused")
		private static <L extends IAction> IcfgProgramExecution<L> createExecution(final List<L> trace,
				final List<Map<Term, Term>> states) {
			// TODO: Don't define our own ProgramState in this plugin, then we can just use a normal import here.
			final Map<Integer, de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState<Term>> stateMapping = new HashMap<>();
			for (int i = 0; i < states.size(); i++) {
				stateMapping.put(i,
						new de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState<>(
								states.get(i).entrySet().stream().collect(
										Collectors.toMap(x -> x.getKey(), x -> List.of(x.getValue()))),
								Term.class));
			}
			return IcfgProgramExecution.create(trace, stateMapping);
		}
	}
}
