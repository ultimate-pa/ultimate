package de.uni_freiburg.informatik.ultimate.pea2boogie.results;

import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResult;
import de.uni_freiburg.informatik.ultimate.pea2boogie.Activator;

/**
 * Report type errors detected during creation of the symbol table. We abort if they occur.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class RequirementTypeErrorResult extends GenericResult {

	public RequirementTypeErrorResult(final String id, final String reason) {
		super(Activator.PLUGIN_ID, "Type error in requirement: " + id,
				"Type error in requirement: " + id + " Reason: " + reason, Severity.ERROR);
	}

	public RequirementTypeErrorResult(final int line, final String reason) {
		super(Activator.PLUGIN_ID, "Type error in line: " + line, "Type error in line: " + line + " Reason: " + reason,
				Severity.ERROR);
	}
}