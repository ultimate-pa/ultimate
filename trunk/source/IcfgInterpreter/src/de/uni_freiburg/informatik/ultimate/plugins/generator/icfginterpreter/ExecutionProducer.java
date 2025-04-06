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
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.compiled.EnumState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.compiled.IVariableName;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.compiled.JavaCodeEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.IcfgExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.IcfgTranslation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.InterpretedIcfg;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences.IcfgInterpreterPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences.Settings;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class ExecutionProducer {
	public interface IIcfgExecutionProducer {
		void init(InterpretedIcfg intIcfg);

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
		producer.init(execIcfg);
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

	public static class CompiledEnumExecutionProducer<T extends Enum<T> & IVariableName>
			implements IIcfgExecutionProducer {
		private HashMap<IcfgLocation, ArrayList<JavaCodeEdge<T>>> compiledEdges;
		private Function<NonDeterministicChoice, EnumState<T>> stateMaker;

		@Override
		public void init(final InterpretedIcfg intIcfg) {
			final HashSet<Variable> variables = intIcfg.getVariables();
			try {
				final Class<T> enumClass = DynamicLoader.makeVariableNameEnum(variables);
				compiledEdges = (DynamicLoader.makeUpdates(intIcfg, enumClass));
				stateMaker = EnumState.getStateInitializer(variables, enumClass);
			} catch (final Exception e) {
				e.printStackTrace();
				return;
			}
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

			return null;
		}

	}

	public static class LiteralExecutionProducer implements IIcfgExecutionProducer {
		private ArrayList<Variable> mVariables;
		private InterpretedIcfg mIIcfg;

		@Override
		public void init(final InterpretedIcfg intIcfg) {
			mVariables = new ArrayList<>(intIcfg.getVariables());
			mIIcfg = intIcfg;
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

				state = nextEdge.execute(state, ndc);
				execution.addStep(state, nextEdge.mTarget, nextEdge.getTransFormula());
				nextEdges.clear();
				nextEdges.addAll(mIIcfg.getOutEdges(nextEdge.mTarget));
			}

			return null;

		}

	}
}
