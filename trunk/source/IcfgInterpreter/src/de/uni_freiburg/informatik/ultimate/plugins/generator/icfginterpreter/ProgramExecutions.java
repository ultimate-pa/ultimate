package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;

// TODO: Better name?
public final class ProgramExecutions<L extends IAction> extends BasePayloadContainer {
	private static final long serialVersionUID = -5577390430583256394L;

	public record Pair<A, B>(A a, B b) {
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
	private final Map<ExecutionTermintionReason, List<IcfgProgramExecution<L>>> mExecutions;

	public ProgramExecutions(final Map<ExecutionTermintionReason, List<IcfgProgramExecution<L>>> executions) {
		mExecutions = executions;
	}

	public Map<ExecutionTermintionReason, List<IcfgProgramExecution<L>>> getExecutions() {
		return mExecutions;
	}
}
