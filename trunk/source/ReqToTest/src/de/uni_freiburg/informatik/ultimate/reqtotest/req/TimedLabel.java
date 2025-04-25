package de.uni_freiburg.informatik.ultimate.reqtotest.req;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class TimedLabel {

	private final Term mGuard;
	private final TermVariable mReset;
	private final boolean mIsEffectEdge;
	private final Term mClockGuard;

	public TimedLabel(final Term guard, final Term clockGuard, final TermVariable reset, final boolean isEffect) {
		mGuard = guard;
		mReset = reset;
		mClockGuard = clockGuard;
		mIsEffectEdge = isEffect;
	}

	public TimedLabel(final Term guard, final Term clockGuard, final TermVariable reset) {
		mGuard = guard;
		mReset = reset;
		mClockGuard = clockGuard;
		mIsEffectEdge = false;
	}

	public TimedLabel(final Term guard, final Term clockGuard, final boolean isEffect) {
		mGuard = guard;
		mReset = null;
		mClockGuard = clockGuard;
		mIsEffectEdge = isEffect;
	}

	public TimedLabel(final Term guard, final Term clockGuard) {
		mGuard = guard;
		mReset = null;
		mClockGuard = clockGuard;
		mIsEffectEdge = false;
	}

	public Term getGuard() {
		return mGuard;
	}

	public Term getClockGuard() {
		return mClockGuard;
	}

	public boolean isEffect() {
		return mIsEffectEdge;
	}

	public TermVariable getReset() {
		return mReset;
	}

	@Override
	public String toString() {
		return "Guard: " + mGuard.toString();
	}
}
