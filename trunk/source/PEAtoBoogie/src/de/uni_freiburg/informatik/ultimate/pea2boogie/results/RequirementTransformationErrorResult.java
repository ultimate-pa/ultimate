package de.uni_freiburg.informatik.ultimate.pea2boogie.results;

import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResult;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.pea2boogie.Activator;

/**
 * Report errors that occurred during the transformation of the requirement to a {@link PhaseEventAutomata}. We just
 * continue after they occur.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class RequirementTransformationErrorResult extends GenericResult {

	public RequirementTransformationErrorResult(final String id, final String reason) {
		super(Activator.PLUGIN_ID, "Ignored requirement due to translation errors: " + id,
				"Ignored requirement due to translation errors: " + id + " Reason: " + reason, Severity.WARNING);
	}
}