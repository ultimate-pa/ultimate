package de.uni_freiburg.informatik.ultimate.btorutils;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class UpdateRule {
	DebugIdentifier targetIdentifier;
	Term condition;

	public UpdateRule(final Term condition, final DebugIdentifier targetIdentifier) {
		this.condition = condition;
		this.targetIdentifier = targetIdentifier;
	}
}
