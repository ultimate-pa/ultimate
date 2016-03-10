package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class WitnessInvariant {

	private final String mInvariant;
	private final Set<String> mNodeLabels;

	public WitnessInvariant(final String invariant, final String nodeLabel) {
		mInvariant = invariant;
		mNodeLabels = new HashSet<String>();
		mNodeLabels.add(nodeLabel);
	}

	public WitnessInvariant(final String invariant, final Collection<String> nodeLabel) {
		mInvariant = invariant;
		mNodeLabels = new HashSet<String>();
		mNodeLabels.addAll(nodeLabel);
	}

	public String getInvariant() {
		return mInvariant;
	}

	public Set<String> getNodeLabel() {
		return mNodeLabels;
	}

	@Override
	public String toString() {
		return mInvariant;
	}
}
