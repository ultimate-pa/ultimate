package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class WitnessInvariant {

	private final String mInvariant;
	private final Set<String> mNodeLabels;
	private final int mEarliestStartline;
	private final int mLatestEndline;

	public WitnessInvariant(final String invariant, final String nodeLabel, final int startline, final int endline) {
		this(invariant, Collections.singleton(nodeLabel), startline, endline);
	}

	public WitnessInvariant(final String invariant, final Collection<String> nodeLabel, final int startline,
			final int endline) {
		mInvariant = invariant;
		mNodeLabels = new HashSet<String>();
		mNodeLabels.addAll(nodeLabel);
		mEarliestStartline = startline;
		mLatestEndline = endline;
	}

	public String getInvariant() {
		return mInvariant;
	}

	public Set<String> getNodeLabels() {
		return mNodeLabels;
	}

	public int getStartline() {
		return mEarliestStartline;
	}

	public int getEndline() {
		return mLatestEndline;
	}

	@Override
	public String toString() {
		return "[L" + mEarliestStartline + "-L" + mLatestEndline + "] " + mInvariant;
	}
}
