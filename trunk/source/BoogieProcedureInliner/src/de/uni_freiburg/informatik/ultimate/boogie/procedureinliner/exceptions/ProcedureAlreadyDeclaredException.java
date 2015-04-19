package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.exceptions;

import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.Activator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.result.AbstractResult;
import de.uni_freiburg.informatik.ultimate.result.UnsupportedSyntaxResult;

/**
 * Indicates that a Boogie procedure was declared more than one time.
 * This shouldn't occur, since the Boogie parser should already complain about it.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class ProcedureAlreadyDeclaredException extends CancelToolchainException {

	private static final long serialVersionUID = 4403766989405696198L;

	public ProcedureAlreadyDeclaredException(Procedure procedure) {
		super("Procedure was already declared: " + procedure.getIdentifier(), procedure.getLocation());
	}
	
	@Override
	protected AbstractResult createResult(String pluginId) {
		return new UnsupportedSyntaxResult<Procedure>(Activator.PLUGIN_ID, getLocation(), getMessage());
	}
}
