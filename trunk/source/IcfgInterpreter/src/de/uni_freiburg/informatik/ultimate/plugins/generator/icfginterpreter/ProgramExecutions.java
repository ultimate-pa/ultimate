package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;

// TODO: Better name?
public final class ProgramExecutions<L extends IAction> extends BasePayloadContainer {
	private static final long serialVersionUID = -5577390430583256394L;

	// TODO: Also include the reason why the executions ended (no outgoing transitions, error, unsupported feature...)
	private final Collection<IcfgProgramExecution<L>> mExecutions;

	public ProgramExecutions(final Collection<IcfgProgramExecution<L>> executions) {
		mExecutions = executions;
	}

	public Collection<IcfgProgramExecution<L>> getExecutions() {
		return mExecutions;
	}
}
