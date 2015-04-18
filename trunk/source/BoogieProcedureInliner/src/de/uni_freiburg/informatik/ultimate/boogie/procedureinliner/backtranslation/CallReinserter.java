package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.backtranslation;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.Iterator;
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
	
	// TODO document
	private Deque<BackTransValue> mPrevBackTranslations = new ArrayDeque<>();
	
	public List<AtomicTraceElement<BoogieASTNode>> recoverInlinedCallsBefore(BackTransValue curBackTrans) {
		List<AtomicTraceElement<BoogieASTNode>> recoveredCalls = new ArrayList<>();
		if (curBackTrans == null) {
			return recoveredCalls;
		}
		boolean entryProcChanged = mPrevBackTranslations.isEmpty()
				|| !curBackTrans.getInlineEntryProcId().equals(mPrevBackTranslations.peek().getInlineEntryProcId());
		if (entryProcChanged) {
			for (CallStatement cs : curBackTrans.getOriginalCallStack()) {
				recoveredCalls.add(makeAtomicCall(cs));
			}
			Collections.reverse(recoveredCalls);
		} else {
			BackTransValue prevBackTrans = mPrevBackTranslations.pop();
			Deque<CallStatement> prevStack = prevBackTrans.getOriginalCallStack();
			Deque<CallStatement> curStack = curBackTrans.getOriginalCallStack();
			if (prevStack != curStack) {
				Iterator<CallStatement> prevStackIterator = prevStack.descendingIterator(); // from stack bottom to top
				Iterator<CallStatement> curStackIterator = curStack.descendingIterator();
				List<AtomicTraceElement<BoogieASTNode>> returns = new ArrayList<>();
				List<AtomicTraceElement<BoogieASTNode>> calls = new ArrayList<>();
				while (prevStackIterator.hasNext() && curStackIterator.hasNext()) {
					CallStatement prevCS = prevStackIterator.next();
					CallStatement curCS = curStackIterator.next();
					if (prevCS != curCS) {
						returns.add(makeAtomicReturn(prevCS));
						calls.add(makeAtomicCall(curCS));
					}
				}
				while (prevStackIterator.hasNext()) {
					returns.add(makeAtomicReturn(prevStackIterator.next()));
				}
				while (curStackIterator.hasNext()) {
					calls.add(makeAtomicCall(curStackIterator.next()));
				}
				Collections.reverse(returns);
				recoveredCalls.addAll(returns);
				recoveredCalls.addAll(calls);
			}
		}
		mPrevBackTranslations.push(curBackTrans);
		return recoveredCalls;
	}
	
	private AtomicTraceElement<BoogieASTNode> makeAtomicCall(CallStatement originalCall) {
		return new AtomicTraceElement<BoogieASTNode>(originalCall, originalCall, StepInfo.PROC_CALL);
	}
	
	private AtomicTraceElement<BoogieASTNode> makeAtomicReturn(CallStatement originalReturn) {
		return new AtomicTraceElement<BoogieASTNode>(originalReturn, originalReturn, StepInfo.PROC_RETURN);
	}
	
	/**
	 * @return Inlined (!) Procedure, from which the last investigated BoogieASTNode
	 *         ({@linkplain #recoverInlinedCallsBefore(BackTransValue)} was inlined.
	 *         null, if the node was part of an inlining entry procedure or wasn't processed by the inliner at all.
	 */
	public String getInlinedProcId() {
		if (mPrevBackTranslations.isEmpty()) {
			return null;
		} else {
			return mPrevBackTranslations.peek().getInlineEntryProcId();			
		}
	}	
}
