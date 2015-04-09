package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.AbstractResult;
import de.uni_freiburg.informatik.ultimate.result.UnsupportedSyntaxResult;

public class InlinePolymorphicException extends CancelToolchainException {

	private static final long serialVersionUID = 6599224094177831810L;

	public InlinePolymorphicException(ILocation location, String procId) {
		super("Polymorphic procedures are not supported: "  + procId, location);
	}

	@Override
	protected AbstractResult createResult(String pluginId) {
		return new UnsupportedSyntaxResult<>(Activator.PLUGIN_ID, getLocation(), getMessage());
	}

}
