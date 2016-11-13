package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.RewriteUtils;

/**
 * Change by deletion.
 */
public class DeleteChange extends ReplaceChange {
	DeleteChange(final IPSTNode node) {
		super(node, RewriteUtils.getDeletionStringWithWhitespaces(node));
	}
	
	@Override
	public String toString() {
		return "Delete " + getNode();
	}
}
