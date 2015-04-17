package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.backtranslation;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.BackTransValue;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.AtomicTraceElement.StepInfo;

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
	
	public List<AtomicTraceElement<BoogieASTNode>> recoverInlinedCallsBefore(BackTransValue curTraceElemBackTransValue) {
		List<AtomicTraceElement<BoogieASTNode>> recoveredCalls = new ArrayList<>();
		if (curTraceElemBackTransValue == null) {
			return recoveredCalls;
		}
		CallStatement oCall = curTraceElemBackTransValue.getOriginalCall();
		if (oCall == null) {
			oCall = mEntryCallDummy;
		}
		if (mUnreturnedInlinedCalls.isEmpty()) {
			if (oCall != mEntryCallDummy) {
				// very first node of the entry procedure was already an inlined call
				recoveredCalls.add(new AtomicTraceElement<BoogieASTNode>(oCall, oCall, StepInfo.PROC_CALL));
				mUnreturnedInlinedCalls.push(mEntryCallDummy);
			}
			mUnreturnedInlinedCalls.push(oCall);
			return recoveredCalls;
		}
		if (oCall != mUnreturnedInlinedCalls.peek()) {
			if (mUnreturnedInlinedCalls.contains(oCall)) {
				// we returned from one (ore more!) inlined calls
				while (mUnreturnedInlinedCalls.peek() != oCall) {
					CallStatement last = mUnreturnedInlinedCalls.pop();
					recoveredCalls.add(new AtomicTraceElement<BoogieASTNode>(last, last, StepInfo.PROC_RETURN));
				}
			} else {
				// we entered a new, inlined call
				mUnreturnedInlinedCalls.push(oCall);
				recoveredCalls.add(new AtomicTraceElement<BoogieASTNode>(oCall, oCall, StepInfo.PROC_CALL));
			}
		}
		return recoveredCalls;
	}
	
	/**
	 * @return Inlined (!) Procedure, from which the last investigated BoogieASTNode
	 *         ({@linkplain #recoverInlinedCallsBefore(BackTransValue)})
	 *         was inlined.
	 *         null, if the node was part of an inlining entry procedure or wasn't processed by the inliner at all.
	 */
	public String getInlinedProcId() {
		if (mUnreturnedInlinedCalls.isEmpty()) {
			return null;
		} else {
			return mUnreturnedInlinedCalls.peek().getMethodName();			
		}
	}
	
}