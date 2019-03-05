package de.uni_freiburg.informatik.ultimate.reqtotest.req;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class TimedLabel{
	
	private final Term mGuard;
	private final TermVariable mReset;
	private final boolean mIsEffectEdge;
	
	public TimedLabel(Term guard, TermVariable reset, boolean isEffect) {
		mGuard = guard;
		mReset = reset;
		mIsEffectEdge = isEffect;
	}
	
	public TimedLabel(Term guard, TermVariable reset) {
		mGuard = guard;
		mReset = reset;
		mIsEffectEdge = false;
	}
	
	public TimedLabel(Term guard, boolean isEffect) {
		mGuard = guard;
		mReset = null;
		mIsEffectEdge = isEffect;
	}
	
	
	public TimedLabel(Term guard) {
		mGuard = guard;
		mReset = null;
		mIsEffectEdge = false;
	}
	
	public Term getGuard() {
		return mGuard;
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