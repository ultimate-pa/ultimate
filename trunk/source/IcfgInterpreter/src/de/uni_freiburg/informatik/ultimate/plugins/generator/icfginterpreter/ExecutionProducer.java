package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Edge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Equation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Equation.SolvedEquation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.IntValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Update;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Update.AssignmentUpdate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Update.HavocUpdate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Value;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences.IcfgInterpreterPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences.Settings;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class ExecutionProducer {
	public interface IIcfgExecutionProducer {
		void init(InterpretedIcfg intIcfg, IUltimateServiceProvider services);

		IcfgProgramExecution<?> makeExecution(NonDeterministicChoice ndc, IcfgLocation source);
	}

	private static boolean printExecution = true;

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
				final ArrayList<JavaCodeEdge<T>> availableEdges = Util.filter(nextEdges, (edge) -> {
					return edge.guard(stateReference);
				});

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
				final ArrayList<ICFGExecutionEdge> availableEdges = Util.filter(nextEdges, (nextEdge) -> {
					return nextEdge.canBeTaken(stateRefernce);
				});

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
		private final HashMap<IcfgLocation, ArrayList<Edge>> mOutEdges = new HashMap<>();

		@Override
		public void init(final InterpretedIcfg intIcfg, final IUltimateServiceProvider services) {
			final IIcfg<? extends IcfgLocation> icfg = intIcfg.getIcfg();

			final Set<? extends IcfgLocation> initialNodes = icfg.getInitialNodes();
			final ManagedScript mngScript = icfg.getCfgSmtToolkit().getManagedScript();

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

					final Term dnf = SmtUtils.toDnf(services, mngScript, formula.getFormula());

					ArrayList<Edge> newOutEdges = new ArrayList<>();
					if (dnf instanceof final ApplicationTerm ap) {
						Term[] andTerms;
						if (ap.getFunction().getName().equals(SMTLIBConstants.OR)) {
							andTerms = ap.getParameters();
						} else {
							andTerms = new Term[] { ap };
						}

						for (int i = 0; i < andTerms.length; i++) {
							andTerms[i] = makeClear(andTerms[i], theory);
						}

						newOutEdges = reduceAndTerms(andTerms, mngScript, services, formula, source, target);
					}
					System.out.println(formula.toStringDirect());
					printDNF(dnf, 0, mngScript, services);
					for (int i = 0; i < newOutEdges.size(); i++) {
						System.out.println("Edge " + (1 + i) + ":");
						System.out.println(newOutEdges.get(i).toString());
					}
					System.out.println("\n\n");
					final ArrayList<Edge> allOutEdges = mOutEdges.getOrDefault(source, new ArrayList<>());
					allOutEdges.addAll(newOutEdges);
					mOutEdges.put(source, allOutEdges);
				}
			}

			mVariables = new ArrayList<>(intIcfg.getVariables());

			mErrorMap = getErrorLocations(intIcfg.getIcfg());
		}

		/**
		 * Remove unnecessary / merge subset branches
		 *
		 * @param andTerms
		 * @param mngScript
		 * @param services
		 * @param formula
		 * @param source
		 * @param target
		 * @return A Term containing the remaining and simplified andTerms. Should there only be one AndTerm left, then
		 *         that AndTerm is returned, otherwise an OrTerm containing the AndTerms is returned.
		 */

		private static ArrayList<Edge> reduceAndTerms(final Term[] andTerms, final ManagedScript mngScript,
				final IUltimateServiceProvider services, final UnmodifiableTransFormula formula,
				final IcfgLocation source, final IcfgLocation target) {
			final ArrayList<Term> out = new ArrayList<>();

			final HashMap<Term, ApplicationTerm> guards = new HashMap<>();
			final HashMap<Term, ApplicationTerm> updates = new HashMap<>();
			boolean hasUpdate = false;

			for (final Term andTerm : andTerms) {
				final ApplicationTerm guard = makeGuardTerm(mngScript, services, andTerm, formula);
				assert !guards.containsKey(andTerm);
				guards.put(andTerm, guard);
				final ApplicationTerm update = makeUpdateTerm((ApplicationTerm) andTerm, formula);
				if (update == null) {
					continue;
				}
				assert !updates.containsKey(andTerm);
				hasUpdate = true;
				updates.put(andTerm, update);
			}

			// if no updates exist, we return the edge using the original TransFormula as the guard
			if (!hasUpdate) {
				final ArrayList<Edge> outList = new ArrayList<>();
				final Theory theory = mngScript.getScript().getTheory();
				final ArrayList<Update> havocUpdates = getHavocUpdates(theory.constant(true, theory.getBooleanSort()),
						formula);
				outList.add(new Edge(substituteProgramVars(formula.getFormula(), formula, mngScript),
						havocUpdates.toArray(new Update[havocUpdates.size()]), source, target));
				return outList;
			}

			// only keep AndTerms that can be fulfilled
			for (final Term subTerm : andTerms) {
				if (!SmtUtils.isFalseLiteral(guards.get(subTerm))) {
					out.add(subTerm);
				}
			}

			// Used to recombine two edges with the same updates via an OrTerm of both guards
			// final HashMap<List<Update>, Edge> updateCache = new HashMap<>();
			final ArrayList<Edge> outList = new ArrayList<>();
			// final Theory theory = mngScript.getScript().getTheory();
			for (final Term outElement : out) {
				final Term guard = guards.get(outElement);
				final Term subbedGuard = substituteProgramVars(guard, formula, mngScript);
				final Update[] edgeUpdates = makeUpdates(updates.get(outElement), formula, mngScript);
				// final List<Update> updatesAsList = Arrays.asList(edgeUpdates);

				/*
				 * if (updateCache.containsKey(updatesAsList)) { final Edge edgeB = updateCache.remove(updatesAsList);
				 *
				 * outList.remove(edgeB); if (SmtUtils.isSubterm(edgeB.getGuardTerm(), subbedGuard)) { // the guard of
				 * edge b is a super term to the new guard, we just use edge b's guard subbedGuard =
				 * edgeB.getGuardTerm(); } else if (!SmtUtils.isSubterm(subbedGuard, edgeB.getGuardTerm())) { // Neither
				 * guard is a super term of the other, use or(guardA, guardB) subbedGuard = theory.or(subbedGuard,
				 * edgeB.getGuardTerm()); } }
				 */

				final Edge newEdge = new Edge(subbedGuard, edgeUpdates, source, target);

				// updateCache.put(updatesAsList, newEdge);
				outList.add(newEdge);
			}
			return outList;
		}

		private static Update[] makeUpdates(final Term updateTerm, final UnmodifiableTransFormula formula,
				final ManagedScript script) {
			final ApplicationTerm appTerm = (ApplicationTerm) updateTerm;

			final HashSet<SolvedEquation> equalities = new HashSet<>();

			if (appTerm.getFunction().getName().equals(SMTLIBConstants.AND)) {
				for (final Term param : appTerm.getParameters()) {
					final ApplicationTerm paramApp = (ApplicationTerm) param;
					ApplicationTerm newEquality;
					switch (paramApp.getFunction().getName()) {
					case "=", "<", "<=", ">", ">=":
						assert paramApp.getParameters().length == 2;
						newEquality = paramApp;
						break;
					case "not":
						final ApplicationTerm subTerm = (ApplicationTerm) paramApp.getParameters()[0];
						assert subTerm.getFunction().getName().equals(SMTLIBConstants.EQUALS);
						assert subTerm.getParameters().length == 2;

						final Theory theory = updateTerm.getTheory();
						newEquality = (ApplicationTerm) theory.term(theory.mDistinct, subTerm.getParameters());
						break;
					default:
						throw new AssertionError();
					}

					equalities.addAll(solveForVars(newEquality, script.getScript()));
				}
			} else {
				equalities.addAll(solveForVars(appTerm, script.getScript()));
			}

			// Equations have to be ordered such that
			// 1. A variable that is defined by a last state value comes before any update that overrides the reqired
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

			for (final SolvedEquation equality : equalities) {
				if (equality.getRhs() instanceof final TermVariable tv
						&& getProgramVar(equality.getLhs(), formula).equals(getProgramVar(tv, formula))) {
					// Equation a' = a is not defining anything, as they are artifacts from terms that contain multiple
					// branches.
					assignableVars.remove(equality.getLhs());
				}
			}

			final ArrayList<SolvedEquation> equationList = new ArrayList<>(equalities.stream().filter((eq) -> {
				return assignableVars.contains(eq.getLhs());
			}).toList());

			// For each equation, the set of InVars / OutVars that are used. They need to come before / after all
			// equations that define these variables.
			final HashMap<SolvedEquation, ArrayList<TermVariable>> neededInVars = new HashMap<>();
			final HashMap<SolvedEquation, ArrayList<TermVariable>> neededOutVars = new HashMap<>();

			final Map<IProgramVar, TermVariable> formulaInVars = formula.getInVars();
			final Map<IProgramVar, TermVariable> formulaOutVars = formula.getOutVars();

			for (final SolvedEquation equation : equationList) {
				final ArrayList<TermVariable> inVars = neededInVars.getOrDefault(equation, new ArrayList<>());
				final ArrayList<TermVariable> outVars = neededOutVars.getOrDefault(equation, new ArrayList<>());
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
				if (neededOutVars.get(eq2).contains(eq2.getLhs())) {
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

				final ArrayList<SolvedEquation> equals = new ArrayList<>();
				final ArrayList<SolvedEquation> inequals = new ArrayList<>();

				for (final SolvedEquation definition : definitions) {
					if (definition.getRelation().equals(RelationSymbol.EQ)) {
						final TermVariable genericVar = getProgramVar(definition.getLhs(), formula).getTermVariable();
						final Term genericTerm = substituteProgramVars(definition.getRhs(), formula, script);
						equals.add(new SolvedEquation(definition.getRelation(), genericVar, genericTerm));
					} else {
						final TermVariable genericVar = getProgramVar(definition.getLhs(), formula).getTermVariable();
						final Term genericTerm = substituteProgramVars(definition.getRhs(), formula, script);
						inequals.add(new SolvedEquation(definition.getRelation(), genericVar, genericTerm));
					}
				}

				// Replace the formula specific TermVariable with its generic global counterpart
				definedVar = getProgramVar(definedVar, formula).getTermVariable();

				if (!equals.isEmpty()) {
					// We have at least one Term that directly defines the variable.
					out.add(new AssignmentUpdate(definedVar,
							substituteProgramVars(equals.get(0).getRhs(), formula, script)));
				} else {
					// We only have bounds for the Term.
					out.add(new HavocUpdate(definedVar, inequals));
				}
			}

			out.addAll(getHavocUpdates(updateTerm, formula));

			return out.toArray(new Update[out.size()]);
		}

		private static ArrayList<Update> getHavocUpdates(final Term updateTerm,
				final UnmodifiableTransFormula formula) {
			final ArrayList<Update> out = new ArrayList<>();
			// Handle cases where there is no OutVar for an InVar (havoc to any value)
			for (final Entry<IProgramVar, TermVariable> inVar : formula.getInVars().entrySet()) {
				if (formula.getOutVars().containsKey(inVar.getKey())) {
					// There is a defining outVar
					continue;
				}
				out.add(new HavocUpdate(inVar.getKey().getTermVariable(), new ArrayList<>()));
			}

			// Handle cases where an OutVar is not defined in the term and can change (havoc to any value)
			final HashSet<TermVariable> containedVars = new HashSet<>(Arrays.asList(updateTerm.getFreeVars()));
			for (final Entry<IProgramVar, TermVariable> outVar : formula.getOutVars().entrySet()) {
				if (containedVars.contains(outVar.getValue())) {
					// The outvar appears in the term
					continue;
				}
				if (formula.getInVars().containsValue(outVar.getValue())) {
					// The outvar is also an invar (can't change)
					continue;
				}
				out.add(new HavocUpdate(outVar.getKey().getTermVariable(), new ArrayList<>()));
			}

			Collections.sort(out, (ud1, ud2) -> {
				return Integer.compare(ud1.getVariable().getName().hashCode(), ud2.getVariable().getName().hashCode());
			});
			return out;
		}

		private static ArrayList<SolvedEquation> solveForVars(final ApplicationTerm term, final Script script) {
			final ArrayList<SolvedEquation> out = new ArrayList<>();

			final RelationSymbol relation = RelationSymbol.convert(term.getFunction().getName());

			for (final TermVariable termVar : term.getFreeVars()) {
				Equation base = new Equation(relation, term.getParameters()[0], term.getParameters()[1]);

				final boolean leftContains = Arrays.asList(base.getLhs().getFreeVars()).contains(termVar);
				final boolean rightContains = Arrays.asList(base.getRhs().getFreeVars()).contains(termVar);

				if (!(leftContains ^ rightContains)) {
					// can't solve if variable appears on both sides (yet)
					continue;
				}

				// make the side that contains the variable the left hand side
				if (!leftContains && rightContains) {
					base = base.swapParameters();
				}

				switch (base.getRelation()) {
				case DISTINCT:
				case EQ:
					SolvedEquation solvedEq;
					if (base.getLhs().getSort().isNumericSort()) {
						solvedEq = solveForSubjectInt(base, termVar, script);
					} else {
						solvedEq = solveForSubjectEquality(base, termVar);
					}
					if (solvedEq == null) {
						continue;
					}
					out.add(solvedEq);
					break;
				case GEQ:
				case GREATER:
				case LEQ:
				case LESS:
					final SolvedEquation solvedComp = solveForSubjectInt(base, termVar, script);
					if (solvedComp == null) {
						continue;
					}
					out.add(solvedComp);
					break;
				default:
					continue;
				}
			}

			return out;
		}

		private static SolvedEquation solveForSubjectEquality(final Equation equation, final TermVariable subject) {
			if (equation.isSolvedFor(subject)) {
				return equation.getSolvedEquation();
			}
			return null;
		}

		private static SolvedEquation solveForSubjectInt(Equation equation, final TermVariable subject,
				final Script script) {
			if (equation.isSolvedFor(subject)) {
				return equation.getSolvedEquation();
			}

			final ApplicationTerm leftApp = (ApplicationTerm) equation.getLhs();

			final ArrayList<Term> lhsTerms = new ArrayList<>();
			final ArrayList<Term> rhsTerms = new ArrayList<>();
			switch (leftApp.getFunction().getName()) {
			case SMTLIBConstants.PLUS:
				final Term[] addedTerms = leftApp.getParameters();

				rhsTerms.add(equation.getRhs());

				for (final Term addedTerm : addedTerms) {
					if (Arrays.asList(addedTerm.getFreeVars()).contains(subject)) {
						lhsTerms.add(addedTerm);
					} else {
						rhsTerms.add(addedTerm);
					}
				}

				if (lhsTerms.size() > 1) {
					// more than one subTerm of the PlusTerm contained the subject
					return null;
				}

				equation = new Equation(equation.getRelation(), lhsTerms.get(0),
						script.term(SMTLIBConstants.MINUS, rhsTerms.toArray(new Term[rhsTerms.size()])));
				break;
			case SMTLIBConstants.MINUS:
				final Term[] subtractedTerms = leftApp.getParameters();
				if (subtractedTerms.length == 1) {
					// negation, -x = y becomes x = -y
					equation = new Equation(equation.getRelation(), subtractedTerms[0],
							script.term(SMTLIBConstants.MINUS, equation.getRhs()));
					break;
				}

				// turn ((x - y) - z) into ((x + (-y)) + (-z)) and use addition definition above

				for (int i = 1; i < subtractedTerms.length; i++) {
					subtractedTerms[i] = script.term(SMTLIBConstants.MINUS, subtractedTerms[i]);
				}

				equation = new Equation(equation.getRelation(), script.term(SMTLIBConstants.PLUS, subtractedTerms),
						equation.getRhs());
				break;
			default:
				return null;
			}

			return solveForSubjectInt(equation, subject, script);
		}

		private static Term substituteProgramVars(final Term term, final UnmodifiableTransFormula formula,
				final ManagedScript script) {
			final HashSet<Entry<IProgramVar, TermVariable>> vars = new HashSet<>(formula.getInVars().entrySet());
			vars.addAll(formula.getOutVars().entrySet());
			final var subst = vars.stream()
					.collect(Collectors.toMap(e -> e.getValue(), e -> e.getKey().getTermVariable()));

			return Substitution.apply(script, subst, term);
		}

		private static IProgramVar getProgramVar(final TermVariable term, final UnmodifiableTransFormula formula) {
			for (final Entry<IProgramVar, TermVariable> outVar : formula.getOutVars().entrySet()) {
				if (outVar.getValue().equals(term)) {
					return outVar.getKey();
				}
			}
			for (final Entry<IProgramVar, TermVariable> outVar : formula.getInVars().entrySet()) {
				if (outVar.getValue().equals(term)) {
					return outVar.getKey();
				}
			}
			return null;
		}

		private static ApplicationTerm makeGuardTerm(final ManagedScript script, final IUltimateServiceProvider service,
				final Term term, final UnmodifiableTransFormula formula) {
			final TransFormulaBuilder formulaBuilder = new TransFormulaBuilder(formula.getInVars(),
					formula.getOutVars(), formula.getNonTheoryConsts().isEmpty(), formula.getNonTheoryConsts(),
					formula.getBranchEncoders().isEmpty(), formula.getBranchEncoders(), false);

			for (final TermVariable termVar : formula.getAuxVars()) {
				formulaBuilder.addAuxVar(termVar);
			}

			formulaBuilder.setFormula(term);
			formulaBuilder.setInfeasibility(formula.isInfeasible());
			final UnmodifiableTransFormula subTermFormula = formulaBuilder.finishConstruction(script);
			return (ApplicationTerm) refineGuardTerm(
					TransFormulaUtils.computeGuardTerm(service, script, subTermFormula, true));
		}

		private static Term refineGuardTerm(final Term guard) {
			// computeGuardTerm likes to turn
			// 0 < term into 1 <= term
			// as well as
			// termA < termB into termA + 1 <= termB
			// This method undoes this behavior.
			if (guard instanceof final ApplicationTerm at) {
				final Theory theory = guard.getTheory();
				final Term[] params = at.getParameters().clone();
				switch (at.getFunction().getName()) {
				case SMTLIBConstants.OR:
				case SMTLIBConstants.AND:
					for (int i = 0; i < params.length; i++) {
						params[i] = refineGuardTerm(params[i]);
					}
					return theory.term(at.getFunction(), params);
				case SMTLIBConstants.LEQ:
					assert params.length == 2;
					if (params[0] instanceof final ConstantTerm ct) {
						final BigInteger value = ((Rational) ct.getValue()).numerator();
						if (value.equals(BigInteger.ONE)) {
							// 1 <= term <==> 1 < term or 1 == term <==> 0 < term
							return theory.term(SMTLIBConstants.LT,
									theory.constant(BigInteger.ZERO, theory.getNumericSort()), params[1]);
						}
					}
					if (params[0] instanceof final ApplicationTerm plus
							&& plus.getFunction().getName().equals(SMTLIBConstants.PLUS)) {
						final Term[] subParams = plus.getParameters();
						if (subParams[subParams.length - 1] instanceof final ConstantTerm ct) {
							final BigInteger value = ((Rational) ct.getValue()).numerator();
							if (value.equals(BigInteger.ONE)) {
								// termA + 1 <= termB <==> termA + 1 < termB or termA + 1 == termB <==> termA < termB
								if (subParams.length == 2) {
									params[0] = subParams[0];
								} else {
									final Term[] newSubParams = new Term[subParams.length - 1];

									for (int i = 0; i < newSubParams.length; i++) {
										newSubParams[i] = subParams[i];
									}

									params[0] = theory.term(SMTLIBConstants.PLUS, newSubParams);
								}

								return theory.term(SMTLIBConstants.LT, params);
							}
						}
					}
				}
			}
			return guard;
		}

		/**
		 * Removes all subterms of an AndTerm that do not contain outvars or auxvars, meaning they are used only as
		 * guards.
		 *
		 * @param term
		 * @return
		 */
		private static ApplicationTerm makeUpdateTerm(final ApplicationTerm term,
				final UnmodifiableTransFormula formula) {
			final Term[] subTerms;
			if (term.getFunction().getName().equals(SMTLIBConstants.AND)) {
				subTerms = term.getParameters();
			} else {
				subTerms = new Term[] { term };
			}

			final HashSet<TermVariable> assignableVars = new HashSet<>(formula.getAuxVars());
			final Collection<TermVariable> inVars = formula.getInVars().values();
			assignableVars
					.addAll(formula.getOutVars().values().stream().filter((entry) -> !inVars.contains(entry)).toList());

			final ArrayList<ApplicationTerm> nonGuardTerms = new ArrayList<>();
			for (final Term subTerm : subTerms) {
				if (!Arrays.asList(subTerm.getFreeVars()).stream().allMatch((var) -> !assignableVars.contains(var))) {
					// not(all vars are not in the assignable vars)
					// => exists var that is in the assignable vars
					// => term has importance for updates
					nonGuardTerms.add((ApplicationTerm) subTerm);
				}
			}

			if (nonGuardTerms.size() > 1) {
				return (ApplicationTerm) term.getTheory().term(SMTLIBConstants.AND,
						nonGuardTerms.toArray(new Term[nonGuardTerms.size()]));
			}
			if (nonGuardTerms.size() == 1) {
				return nonGuardTerms.get(0);
			}
			return null;
		}

		private void printDNF(final Term term, final int depth, final ManagedScript script,
				final IUltimateServiceProvider service) {
			final String indent = "\t".repeat(depth);
			switch (term) {
			case final ApplicationTerm at:
				if (at.getFunction().getName().equals(SMTLIBConstants.OR)) {
					System.out.println(indent + "(or");
					for (final Term subTerm : at.getParameters()) {
						printDNF(subTerm, depth + 1, script, service);
					}
					System.out.println(indent + ")");
				} else if (at.getFunction().getName().equals(SMTLIBConstants.AND)) {
					System.out.println(indent + "(and");
					for (final Term subTerm : at.getParameters()) {
						printDNF(subTerm, depth + 1, script, service);
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

		private static Term makeClear(final Term term, final Theory theory) {
			if (term instanceof final ApplicationTerm andTerm
					&& andTerm.getFunction().getName().equals(SMTLIBConstants.AND)) {
				final Term[] subTerms = andTerm.getParameters();
				for (int i = 0; i < subTerms.length; i++) {
					subTerms[i] = makeClear(subTerms[i], theory);
				}
				return theory.and(subTerms);
			} else if (term instanceof final TermVariable tv) {
				// and(..., var, ...) => and(..., var = true, ...)
				assert tv.getSort().getName().equals(SMTLIBConstants.BOOL);
				return theory.term("=", tv, theory.term("true"));
			} else if (term instanceof final ApplicationTerm select
					&& select.getFunction().getName().equals(SMTLIBConstants.SELECT)) {
				// and(..., (select arr key), ...) => and(..., (select arr key) = true, ...)
				assert select.getSort().getName().equals(SMTLIBConstants.BOOL);
				return theory.term("=", select, theory.term("true"));
			} else if (term instanceof final ApplicationTerm notTerm
					&& notTerm.getFunction().getName().equals(SMTLIBConstants.NOT)) {
				if (notTerm.getParameters()[0] instanceof final TermVariable tv) {
					// and(..., not(var), ...) => and(..., var = false, ...)
					return theory.term("=", tv, theory.term("false"));
				} else if (notTerm.getParameters()[0] instanceof final ApplicationTerm select
						&& select.getFunction().getName().equals(SMTLIBConstants.SELECT)) {
					// and(..., not(select arr key), ...) => and(..., (select arr key) = false, ...)
					assert select.getSort().getName().equals(SMTLIBConstants.BOOL);
					return theory.term("=", select, theory.term("false"));
				}
			}
			return term;
		}

		private HashMap<TermVariable, Value> makeState(final NonDeterministicChoice ndc) {
			final HashMap<TermVariable, Value> state = new HashMap<>();

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

		@Override
		public IcfgProgramExecution<?> makeExecution(final NonDeterministicChoice ndc, final IcfgLocation source) {
			HashMap<TermVariable, Value> state = makeState(ndc);

			final ArrayList<Edge> nextEdges = new ArrayList<>(mOutEdges.getOrDefault(source, new ArrayList<>()));
			final ArrayList<HashMap<TermVariable, Value>> states = new ArrayList<>();
			final ArrayList<Edge> edges = new ArrayList<>();

			states.add(state);

			while (!nextEdges.isEmpty()) {
				final HashMap<TermVariable, Value> stateReference = state;
				final ArrayList<Edge> availableEdges = Util.filter(nextEdges, (nextEdge) -> {
					return nextEdge.guard(stateReference, ndc);
				});

				Edge nextEdge;
				if (availableEdges.size() > 1) {
					nextEdge = ndc.chooseEdge(availableEdges);
				} else if (availableEdges.size() == 0) {
					// No guard was true, or no edges exist from the current vertex
					break;
				} else {
					nextEdge = availableEdges.get(0);
				}

				edges.add(nextEdge);
				state = nextEdge.update(state, ndc);
				states.add(state);

				nextEdges.clear();
				nextEdges.addAll(mOutEdges.getOrDefault(nextEdge.mTarget, new ArrayList<>()));
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
			final IcfgLocation finalLocation = edges.getLast().mTarget;
			if (mErrorMap.getOrDefault(finalLocation.getProcedure(), new HashSet<>()).contains(finalLocation)) {
				IcfgInterpreterObserver.getLogger()
						.error("Execution successfully ended at error location " + finalLocation.toString());
			}
			// TODO: Store for each Edge the edge in the CFG
			// TODO: Call createExecution then (requires matching types for the states)
			return null;
		}

		private static <L extends IAction> IcfgProgramExecution<L> createExecution(final List<L> trace,
				final List<Map<Term, Term>> states) {
			// TODO: Don't define our own ProgramState in this plugin, then we can just use a normal import here.
			final Map<Integer, de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState<Term>> stateMapping =
					new HashMap<>();
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
