package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.exceptions;

import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.Activator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.result.AbstractResult;
import de.uni_freiburg.informatik.ultimate.result.UnsupportedSyntaxResult;

/**
 * Exception to be thrown on attempt to inline calls to procedures with "free requires" statements.
 * 
 * "free requires PRE" cannot be inlined, because PRE should be only assumed on side of the callee,
 * but not on the side of the caller. This can't be realized without having separate procedures.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class InlineFreeRequiresException extends CancelToolchainException {

	private static final long serialVersionUID = 5590651432963251079L;

	public InlineFreeRequiresException(CallStatement call) {
		super("Calls to procedures with \'free requires\' statements cannot be inlined: " + call, call.getLocation());
	}

	@Override
	protected AbstractResult createResult(String pluginId) {
		return new UnsupportedSyntaxResult<>(Activator.PLUGIN_ID, getLocation(), getMessage());
	}
}
