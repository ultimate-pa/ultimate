package de.uni_freiburg.informatik.ultimate.reqtotest.req;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class TimedLabel{
	
	private final Term mGuard;
	private final TermVariable mReset;
	private final boolean mIsEffectEdge;
	private final Term mClockGuard;
	
	public TimedLabel(Term guard, Term clockGuard, TermVariable reset, boolean isEffect) {
		mGuard = guard;
		mReset = reset;
		mClockGuard = clockGuard;
		mIsEffectEdge = isEffect;
	}
	
	public TimedLabel(Term guard, Term clockGuard, TermVariable reset) {
		mGuard = guard;
		mReset = reset;
		mClockGuard = clockGuard;
		mIsEffectEdge = false;
	}
	
	public TimedLabel(Term guard, Term clockGuard, boolean isEffect) {
		mGuard = guard;
		mReset = null;
		mClockGuard = clockGuard;
		mIsEffectEdge = isEffect;
	}
	
	public TimedLabel(Term guard, Term clockGuard) {
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