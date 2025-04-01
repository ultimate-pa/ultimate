package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Random;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.compiled.EnumState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.compiled.JavaCodeEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.compiled.IVariableName;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.IcfgExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.IcfgTranslation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences.IcfgInterpreterPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences.Settings;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class ExecutionProducer {
	public static <T extends Enum<T> & IVariableName> void makeExecutions(
			final IIcfg<? extends IcfgLocation> icfg, final IUltimateServiceProvider services, final ILogger logger) {
		IcfgInterpreterPreferences.updatePreferences();
		final int testExecutionCount = Math.max(1, IcfgInterpreterPreferences.getPreferences()
				.getInt(IcfgInterpreterPreferences.SettingLabel.EXECUTIONS_PER_ENTRYPOINT.toString(), 5));

		logger.info("Creating " + testExecutionCount + " executions per initial node.");

		final HashMap<IcfgLocation, ArrayList<ICFGExecutionEdge>> sourceToEdge = IcfgTranslation.edgeBFS(icfg,
				services);

		final Set<? extends IcfgLocation> initialNodes = icfg.getInitialNodes();
		final NonDeterministicChoice ndc = Settings.getSettings().getNDC();
		final Random random = new Random();
		final long sharedSeed = random.nextLong();

		final HashSet<Variable> allVariables = new HashSet<>();

		for (final IcfgLocation node : initialNodes) {
			for (final ICFGExecutionEdge outEdge : sourceToEdge.get(node)) {
				allVariables.addAll(outEdge.getReachableVariables());
			}
		}

		final HashMap<IcfgLocation, ArrayList<JavaCodeEdge<T>>> compiledEdgesB;
		final Class<T> enumClass;
		try {
			enumClass = DynamicLoader.makeVariableNameEnum(allVariables);
			compiledEdgesB = (DynamicLoader.makeUpdates(sourceToEdge, enumClass));
		} catch (final Exception e) {
			e.printStackTrace();
			return;
		}

		final HashSet<IProgramVar> arrayVars = new HashSet<>();
		final HashSet<IProgramVar> intVars = new HashSet<>();
		final HashSet<IProgramVar> boolVars = new HashSet<>();
		final HashSet<IProgramVar> bvVars = new HashSet<>();
		for (final Variable variable : allVariables) {
			final IProgramVar programVar = variable.getVariableTerm().programVar;
			if (programVar == null) {
				continue;
			}
			switch (variable.getTerm().returnType) {
			case Array:
				arrayVars.add(programVar);
				break;
			case BitVector:
				bvVars.add(programVar);
				break;
			case Boolean:
				boolVars.add(programVar);
				break;
			case Int:
				intVars.add(programVar);
				break;
			}
		}

		final Random randomA = new Random(sharedSeed);
		final Function<NonDeterministicChoice, EnumState<T>> stateMakerB = EnumState.getStateInitializer(arrayVars,
				intVars, boolVars, bvVars, enumClass);

		long startTime = System.nanoTime();
		for (final IcfgLocation node : initialNodes) {
			for (final JavaCodeEdge<T> outEdge : compiledEdgesB.get(node)) {
				for (int i = 0; i < testExecutionCount; i++) {
					final long seed = randomA.nextLong();
					final NonDeterministicChoice ndcInstance = ndc.newInstance(seed);
					makeExecutionEnumCompiled(stateMakerB, ndcInstance, outEdge, compiledEdgesB);
				}
			}
		}
		long endTime = System.nanoTime();
		long totalTime = endTime - startTime;
		logger.info("Enum + compiled total time was " + (totalTime / 1000000.0) + "ms");
		totalTime = 0;

		final Random randomB = new Random(sharedSeed);

		startTime = System.nanoTime();
		for (final IcfgLocation node : initialNodes) {
			for (final ICFGExecutionEdge outEdge : sourceToEdge.get(node)) {

				for (int i = 0; i < testExecutionCount; i++) {

					final long seed = randomB.nextLong();
					final NonDeterministicChoice ndcInstance = ndc.newInstance(seed);
					makeExecutionOld(ndcInstance, outEdge, node, allVariables, sourceToEdge);

				}

			}
		}
		endTime = System.nanoTime();
		totalTime = endTime - startTime;

		logger.info("Uncompiled total time was " + (totalTime / 1000000.0) + "ms");
	}

	private static <T extends Enum<T> & IVariableName> IcfgProgramExecution<?> makeExecutionEnumCompiled(
			final Function<NonDeterministicChoice, EnumState<T>> stateMaker, final NonDeterministicChoice ndc,
			final JavaCodeEdge<T> outEdge, final HashMap<IcfgLocation, ArrayList<JavaCodeEdge<T>>> compiledEdges) {
		final ArrayList<EnumState<T>> states = new ArrayList<>();
		final ArrayList<JavaCodeEdge<T>> edges = new ArrayList<>();
		EnumState<T> state = stateMaker.apply(ndc);
		states.add(state);

		ArrayList<JavaCodeEdge<T>> nextEdges = new ArrayList<>();
		nextEdges.add(outEdge);

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

		return null;
	}

	private static IcfgProgramExecution<?> makeExecutionOld(final NonDeterministicChoice ndc,
			final ICFGExecutionEdge edge, final IcfgLocation node, final HashSet<Variable> allVariables,
			final HashMap<IcfgLocation, ArrayList<ICFGExecutionEdge>> sourceToEdge) {
		ProgramState state = new ProgramState(new ArrayList<>(allVariables), ndc);
		state.finalizeState();
		final IcfgExecution execution = new IcfgExecution(state, node);

		final ArrayList<ICFGExecutionEdge> nextEdges = new ArrayList<>();
		nextEdges.add(edge);

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

			state = nextEdge.execute(state, ndc);
			execution.addStep(state, nextEdge.mTarget, nextEdge.getTransFormula());
			nextEdges.clear();
			nextEdges.addAll(sourceToEdge.getOrDefault(nextEdge.mTarget, new ArrayList<>()));
		}

		return null;
	}
}
