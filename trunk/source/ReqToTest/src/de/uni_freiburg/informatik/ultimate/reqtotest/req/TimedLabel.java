package de.uni_freiburg.informatik.ultimate.reqtotest.req;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class TimedLabel{
	
	private final Term mGuard;
	private final TermVariable mReset;
	
	public TimedLabel(Term guard, TermVariable reset) {
		mGuard = guard;
		mReset = reset;
	}
	
	public TimedLabel(Term guard) {
		mGuard = guard;
		mReset = null;
	}
	
	public Term getGuard() {
		return mGuard;
	}
	
	public TermVariable getReset() {
		return mReset;
	}
}