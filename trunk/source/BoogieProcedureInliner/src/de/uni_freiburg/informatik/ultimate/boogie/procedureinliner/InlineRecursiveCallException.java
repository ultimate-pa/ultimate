package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.result.AbstractResult;
import de.uni_freiburg.informatik.ultimate.result.UnsupportedSyntaxResult;

public class InlineRecursiveCallException extends CancelToolchainException {

	private static final long serialVersionUID = -4670415105408860398L;

	public InlineRecursiveCallException(CallStatement call) {
		super("Inlining calls to recursive procedures is not supported.", call.getLocation());
	}

	@Override
	protected AbstractResult createResult(String pluginId) {
		return new UnsupportedSyntaxResult<>(Activator.PLUGIN_ID, getLocation(), getMessage());
	}

}
