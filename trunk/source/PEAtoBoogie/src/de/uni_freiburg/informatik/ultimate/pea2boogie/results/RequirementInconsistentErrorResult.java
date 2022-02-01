package de.uni_freiburg.informatik.ultimate.pea2boogie.results;

import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResult;
import de.uni_freiburg.informatik.ultimate.pea2boogie.Activator;
import de.uni_freiburg.informatik.ultimate.pea2boogie.generator.RtInconcistencyConditionGenerator.InvariantInfeasibleException;

public final class RequirementInconsistentErrorResult extends GenericResult {

	private final Set<String> mIds;

	public RequirementInconsistentErrorResult(final InvariantInfeasibleException ex) {
		super(Activator.PLUGIN_ID, "Requirements set is inconsistent.",
				"Requirements set is inconsistent. " + ex.getMessage(), Severity.ERROR);
		mIds = ex.getResponsibleRequirements().stream().map(a -> a.getId()).collect(Collectors.toSet());
	}

	public Set<String> getIds() {
		return mIds;
	}
}