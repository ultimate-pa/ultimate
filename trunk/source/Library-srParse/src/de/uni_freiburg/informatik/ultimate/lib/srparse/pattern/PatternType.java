package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.reqcheck.PatternToPEA;
import de.uni_freiburg.informatik.ultimate.lib.srparse.srParseScope;

public class PatternType {
	// contains all CDDs from the patter in reverse order
	protected List<CDD> mCdds;

	protected static final CDD DEFAULT_Q = BooleanDecision.create("Q");
	protected static final CDD DEFAULT_R = BooleanDecision.create("R");
	protected int mDuration;
	protected PhaseEventAutomata mPea;
	protected int mEffectOffset;

	protected srParseScope mScope;
	protected PatternToPEA mPeaTransformator;
	protected CDD mEffect;

	private String mId;

	public PatternType() {
		this(null);
	}

	public PatternType(final srParseScope scope) {
		mScope = scope;
	}

	public int getEffectOffset() {
		return mEffectOffset;
	}

	/***
	 * Determine if a variable name is in the set of variables that are affected by the requirement.
	 *
	 * @param ident
	 *            identifier of variable
	 * @return true if the Variable's value is determined by this requirements effect.
	 */
	public boolean isEffect(final String ident) {
		return mEffect.getIdents().contains(ident);
	}

	public Set<String> getEffectVariabels() {
		return mEffect.getIdents();
	}

	public CDD getEffect() {
		return mEffect;
	}

	public int getDuration() {
		return mDuration;
	}

	public List<CDD> getCdds() {
		return mCdds;
	}

	public void setDuration(final int duration) {
		mDuration = duration;
	}

	public void transform() {
		throw new UnsupportedOperationException();
	}

	public void mergeCDDs(final List<CDD> cdds) {
		if (cdds == null) {
			return;
		}
		if (mCdds == null) {
			mCdds = new ArrayList<>();
		}
		for (int i = 0; i < cdds.size(); i++) {
			mCdds.add(cdds.get(i));
		}
	}

	public PhaseEventAutomata transformToPea() {
		transform();
		return mPea;
	}

	public PatternToPEA getPeaTransformator() {
		return mPeaTransformator;
	}

	public void setPeaTransformator(final PatternToPEA peaTransformator) {
		mPeaTransformator = peaTransformator;
	}

	public srParseScope getScope() {
		return mScope;
	}

	public void setScope(final srParseScope scope) {
		mScope = scope;
	}

	@Override
	public String toString() {
		assert mScope != null || this instanceof InitializationPattern;
		if (mScope == null) {
			return getClass().toString();
		}
		return mScope.toString() + this.getClass().toString();
	}

	public void setId(final String id) {
		mId = id;
	}

	public String getId() {
		return mId;
	}
}
