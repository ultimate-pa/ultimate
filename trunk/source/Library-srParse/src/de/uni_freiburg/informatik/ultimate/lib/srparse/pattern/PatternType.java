package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.Collections;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.BoundTypes;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.DCPhase;
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

	public CDD[] getCddsAsArray() {
		return getCdds().toArray(new CDD[getCdds().size()]);
	}

	public String[] getDurationsAsArray() {
		return getDuration().toArray(new String[getDuration().size()]);
	}

	public int[] getDurationsAsIntArray(final Map<String, Integer> id2bounds) {
		final String[] durations = getDurationsAsArray();
		final int[] rtr = new int[durations.length];
		for (int i = 0; i < durations.length; ++i) {
			rtr[i] = parseDuration(durations[i], id2bounds);
		}
		return rtr;
	}

	public String getId() {
		return mId;
	}

	public SrParseScope getScope() {
		return mScope;
	}

	protected abstract PhaseEventAutomata transform(PatternToPEA peaTrans, final Map<String, Integer> id2bounds);

	public abstract PatternType rename(String newName);

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
						mId + ": Cannot parse duration and alternative bounds do not contain " + duration);
			}
			return actualDuration;
		}
	}

	protected PhaseEventAutomata compile(final PatternToPEA peaTrans, final CounterTrace ct) {
		return peaTrans.compile(getId() + "_" + createPeaSuffix(), ct);
	}

	private String createPeaSuffix() {
		final String suffix;
		if (mScope == null) {
			suffix = "NoScope";
		} else {
			// remove SrParseScope from scope class name
			suffix = mScope.getClass().getSimpleName().substring(12);
		}
		final String className = getClass().getSimpleName();
		return suffix + "_" + className.replaceAll("Pattern", "");
	}

	protected static CounterTrace counterTrace(final CounterTrace.DCPhase... phases) {
		if (phases == null || phases.length == 0) {
			throw new IllegalArgumentException("Need at least one phase");
		}
		return new CounterTrace(phases);
	}

	protected static CounterTrace counterTrace(final CDD... cdds) {
		if (cdds == null || cdds.length == 0) {
			throw new IllegalArgumentException("Need at least one phase");
		}
		final DCPhase[] phases = new DCPhase[cdds.length];
		for (int i = 0; i < cdds.length; ++i) {
			phases[i] = phase(cdds[i]);
		}
		return new CounterTrace(phases);
	}

	protected static DCPhase phase(final CDD x) {
		return new CounterTrace.DCPhase(x);
	}

	protected static DCPhase phase(final CDD x, final BoundTypes boundType, final int duration) {
		return new CounterTrace.DCPhase(x, boundType.asValue(), duration);
	}

	/**
	 * @return A phase with bound that can be empty
	 */
	protected static DCPhase phaseE(final CDD x, final BoundTypes boundType, final int duration) {
		return new CounterTrace.DCPhase(CDD.TRUE, x, boundType.asValue(), duration, Collections.emptySet(), true);
	}

	/**
	 * @return A true-{@link DCPhase} that can be empty.
	 */
	protected static DCPhase phaseT() {
		return new CounterTrace.DCPhase();
	}

	protected static CDD cddT() {
		return CDD.TRUE;
	}

	@Override
	public String toString() {
		assert getScope() != null || this instanceof InitializationPattern;
		if (getScope() == null) {
			return getClass().toString();
		}
		return getScope().toString() + getClass().toString();
	}

	@Override
	public int hashCode() {
		// note that mId and mPea are deliberately not part of the hash code or the equality comparison
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mCdds == null) ? 0 : mCdds.hashCode());
		result = prime * result + ((mDurations == null) ? 0 : mDurations.hashCode());
		result = prime * result + ((mScope == null) ? 0 : mScope.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		// note that mId and mPea are deliberately not part of the hash code or the equality comparison
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final PatternType other = (PatternType) obj;
		if (mDurations == null) {
			if (other.mDurations != null) {
				return false;
			}
		} else if (!mDurations.equals(other.mDurations)) {
			return false;
		}
		if (mScope == null) {
			if (other.mScope != null) {
				return false;
			}
		} else if (!mScope.equals(other.mScope)) {
			return false;
		}
		if (mCdds == null) {
			if (other.mCdds != null) {
				return false;
			}
		} else if (!mCdds.equals(other.mCdds)) {
			return false;
		}
		return true;
	}

}
