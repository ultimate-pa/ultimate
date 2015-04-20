package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.exceptions;

import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.Activator;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.AbstractResult;
import de.uni_freiburg.informatik.ultimate.result.UnsupportedSyntaxResult;

/**
 * Indicates that a part of the program couldn't be inlined, and that the toolchain should be canceled.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class InliningUnsupportedException extends CancelToolchainException {

	private static final long serialVersionUID = 7795426075105131787L;

	public InliningUnsupportedException(String message, ILocation location) {
		super("Inlining unsupported: " + message, location);
	}

	@Override
	protected AbstractResult createResult(String pluginId) {
		return new UnsupportedSyntaxResult<>(Activator.PLUGIN_ID, getLocation(), getMessage());
	}
}
