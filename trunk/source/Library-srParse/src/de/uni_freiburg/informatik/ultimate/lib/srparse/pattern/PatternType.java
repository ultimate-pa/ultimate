package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.Collections;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.reqcheck.PatternToPEA;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;

public abstract class PatternType {

	protected static final CDD DEFAULT_Q = BooleanDecision.create("Q");
	protected static final CDD DEFAULT_R = BooleanDecision.create("R");

	// contains all CDDs from the pattern in reverse order
	private final List<CDD> mCdds;
	private final List<String> mDurations;
	private final SrParseScope mScope;
	private final String mId;

	private PhaseEventAutomata mPea;

	public PatternType(final SrParseScope scope, final String id, final List<CDD> cdds, final List<String> durations) {
		mScope = scope;
		mId = id;
		mCdds = cdds;
		mDurations = durations;
	}

	public List<String> getDuration() {
		return Collections.unmodifiableList(mDurations);
	}

	public List<CDD> getCdds() {
		return Collections.unmodifiableList(mCdds);
	}

	public String getId() {
		return mId;
	}

	public SrParseScope getScope() {
		return mScope;
	}

	protected abstract PhaseEventAutomata transform(PatternToPEA peaTrans, final Map<String, Integer> id2bounds);

	public PhaseEventAutomata transformToPea(final PatternToPEA peaTrans, final Map<String, Integer> id2bounds) {
		if (mPea == null) {
			mPea = transform(peaTrans, id2bounds);
		}
		return mPea;
	}

	protected int parseDuration(final String duration, final Map<String, Integer> id2bounds) {
		if (duration == null) {
			throw new IllegalArgumentException("Duration cannot be null");
		}
		try {
			return Integer.parseInt(duration);
		} catch (final NumberFormatException nfe) {
			if (id2bounds == null) {
				throw new IllegalArgumentException("Cannot parse duration and no alternative bounds are given");
			}
			final Integer actualDuration = id2bounds.get(duration);
			if (actualDuration == null) {
				throw new IllegalArgumentException(
						"Cannot parse duration and alternative bounds do not contain " + duration);
			}
			return actualDuration;
		}
	}

	@Override
	public String toString() {
		assert getScope() != null || this instanceof InitializationPattern;
		if (getScope() == null) {
			return getClass().toString();
		}
		return getScope().toString() + getClass().toString();
	}

}
