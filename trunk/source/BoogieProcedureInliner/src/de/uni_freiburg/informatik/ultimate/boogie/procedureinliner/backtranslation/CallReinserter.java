package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.backtranslation;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.BackTransValue;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;

/**
 * Analyzes a trace from an inlined boogie program and offers calls to be inserted,
 * before/after an new inlined call begins/ends.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class CallReinserter {

	private Deque<CallStatement> mUnreturnedInlinedCalls = new ArrayDeque<>();
	
	/**
	 * Inlining entry points have no {@link BackTransValue#getOriginalCall()}, which is represented using null.
	 * null cannot be added to a Collection and is therefore replace with this instance.
	 */
	private final CallStatement mEntryCallDummy = new CallStatement(null, false, null, null, null);
	
	public List<CallStatement> recoverInlinedCallsBefore(BackTransValue curTraceElemBackTransValue) {
		List<CallStatement> recoveredCalls = new ArrayList<>();			
		if (curTraceElemBackTransValue == null) {
			return recoveredCalls;
		}
		CallStatement oCall = curTraceElemBackTransValue.getOriginalCall();
		if (oCall == null) {
			oCall = mEntryCallDummy;
		}
		if (mUnreturnedInlinedCalls.isEmpty()) {
			mUnreturnedInlinedCalls.push(oCall);
			return recoveredCalls;
		}
		if (oCall != mUnreturnedInlinedCalls.peek()) {
			if (mUnreturnedInlinedCalls.contains(oCall)) {
				// we returned from one (ore more!) inlined calls
				CallStatement last;
				while ((last = mUnreturnedInlinedCalls.pop()) != oCall) {
					if (last.getLhs().length > 0) {
						recoveredCalls.add(last);						
					}
				}
			} else {
				// we entered a new, inlined call
				mUnreturnedInlinedCalls.push(oCall);
				recoveredCalls.add(oCall);
			}
		}
		return recoveredCalls;
	}
	
}