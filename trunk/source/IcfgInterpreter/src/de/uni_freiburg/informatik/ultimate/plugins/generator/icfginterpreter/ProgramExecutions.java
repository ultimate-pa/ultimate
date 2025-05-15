package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;

// TODO: Better name?
public final class ProgramExecutions<L extends IAction> extends BasePayloadContainer {
	private static final long serialVersionUID = -5577390430583256394L;

	public record Pair<A, B>(A a, B b) {
	}

	public enum ExecutionTermintionReason {
		/** Execution has not been terminated yet */
		unterminated,
		/** Execution arrived at leaf of ICFG that is not an error location */
		reachedExit,
		/** Execution arrived at leaf of ICFG that is an error location */
		reachedError,
		/** Execution ended at node where all outgoing edges cannot be fulfilled */
		noEdgeAllowed,
		/** Execution ended on edge that could not be translated */
		edgeUnusble,
		/** Execution ended when an unsupported term was evaluated */
		unsopportedOperation
	}

	// TODO: Also include the reason why the executions ended (no outgoing transitions, error, unsupported feature...)
	private final Collection<Pair<IcfgProgramExecution<L>, ExecutionTermintionReason>> mExecutions;

	public ProgramExecutions(final Collection<Pair<IcfgProgramExecution<L>, ExecutionTermintionReason>> executions) {
		mExecutions = executions;
	}

	public Collection<Pair<IcfgProgramExecution<L>, ExecutionTermintionReason>> getExecutions() {
		return mExecutions;
	}
}
