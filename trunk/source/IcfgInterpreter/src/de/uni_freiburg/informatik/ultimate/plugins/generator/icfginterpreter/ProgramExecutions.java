package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ExecutionProducer.PartialExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datastructures.Value;

// TODO: Better name?
public final class ProgramExecutions extends BasePayloadContainer {
	private static final long serialVersionUID = -5577390430583256394L;

	public record Pair<A, B>(A a, B b) {
		@Override
		public boolean equals(final Object other) {
			if (other instanceof final Pair p) {
				return a == p.a() && b == p.b();
			}
			return false;
		}
	}

	public record Triple<A, B, C>(A a, B b, C c) {
		@Override
		public boolean equals(final Object other) {
			if (other instanceof final Triple t) {
				return a == t.a() && b == t.b() && c == t.c();
			}
			return false;
		}
	}

	public enum ExecutionTermintionReason {
		/** Execution arrived at location where no next edge of ICFG can be taken, it is not an error location */
		REACHED_EXIT,
		/** Execution arrived at error location of ICFG */
		REACHED_ERROR,
		/** Execution ended when an unsupported term was evaluated / not translatable edge was encountered */
		REACHED_UNSUPPORTED,
		/** Execution was interrupted after reaching max length given in settings */
		EXECUTION_TOO_LONG
	}

	// TODO: Also include the reason why the executions ended (no outgoing transitions, error, unsupported feature...)
	private final Map<ExecutionTermintionReason, List<PartialExecution>> mExecutions;

	public ProgramExecutions(final Map<ExecutionTermintionReason, List<PartialExecution>> executions) {
		mExecutions = executions;
	}

	public Map<ExecutionTermintionReason, List<PartialExecution>> getExecutions() {
		return mExecutions;
	}

	public static IcfgProgramExecution<IcfgEdge> translateExecution(final PartialExecution execution,
			final ManagedScript script) {
		// Execution must be finished
		assert execution.status() != null;

		final List<Map<Term, Term>> states =
				execution.states().stream().map(stateUncast -> castMap(stateUncast, script)).toList();
		final List<IcfgEdge> trace = execution.edges().stream().map(intEdge -> intEdge.getEdge()).toList();

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

	private static Map<Term, Term> castMap(final Map<TermVariable, Value> state, final ManagedScript mngScript) {
		final HashMap<Term, Term> out = new HashMap<>();

		for (final Entry<TermVariable, Value> entry : state.entrySet()) {
			out.putAll(entry.getValue().toTerm(mngScript.getScript(), entry.getKey()));
		}

		return out;
	}
}
