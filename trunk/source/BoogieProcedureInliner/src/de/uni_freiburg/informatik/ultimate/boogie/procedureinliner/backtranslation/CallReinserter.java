/*
 * Copyright (C) 2015 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogieProcedureInliner plug-in.
 *
 * The ULTIMATE BoogieProcedureInliner plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogieProcedureInliner plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieProcedureInliner plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieProcedureInliner plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogieProcedureInliner plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.backtranslation;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.BackTransValue;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.InlinedCallAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IRelevanceInformation;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.AtomicTraceElementBuilder;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.StepInfo;

/**
 * Analyzes a trace from an inlined Boogie program and offers calls/returns to be inserted before a new inlined call
 * begins/ends.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class CallReinserter {

	/**
	 * Last BackTransValues for all trace sections with the same inline entry point.
	 * <p>
	 * There is a {@link BackTransValue} for every unreturned non-inlined call. The stack height increases after (!)
	 * non-inlined calls and decreases before non-inlined returns.
	 */
	private final Deque<BackTransValue> mPrevBackTranslations = new ArrayDeque<>();

	/**
	 * Needs to be called for every trace element and in the order of the trace to work correctly.
	 *
	 * @param curTraceElem
	 *            Current trace element.
	 * @param curBackTrans
	 *            trace element's value from the backtranslation map.
	 * @param relevanceInfoForInlinedReturn
	 *            relevance information for inlined return statements collected by the caller
	 * @return CallStatements to be inserted before the current trace element.
	 */
	public List<AtomicTraceElement<BoogieASTNode>> recoverInlinedCallsBefore(
			final AtomicTraceElement<BoogieASTNode> curTraceElem, final BackTransValue curBackTrans,
			final IRelevanceInformation relevanceInfoForInlinedReturn) {

		final boolean nonInlinedCall = curTraceElem.hasStepInfo(StepInfo.PROC_CALL);
		final boolean nonInlinedReturn = curTraceElem.hasStepInfo(StepInfo.PROC_RETURN);
		assert !(nonInlinedCall && nonInlinedReturn) : "Simultaneous call and return: " + curTraceElem;

		// TODO: It would be much cleaner to rely completely on the InlinedCallAnnotations to make the backtranslation.
		// This is more of a quick fix.
		final InlinedCallAnnotation callAnnot = InlinedCallAnnotation.getAnnotation(curTraceElem.getTraceElement());
		if (callAnnot == null) {
			return Collections.emptyList();
		}
		final AtomicTraceElementBuilder<BoogieASTNode> ateBuilder = new AtomicTraceElementBuilder<>();
		ateBuilder.setToStringFunc(BoogiePrettyPrinter.getBoogieToStringProvider());
		ateBuilder.setStepAndElement(callAnnot.getCallStatement());

		if (curTraceElem.hasThreadId()) {
			ateBuilder.setThreadId(curTraceElem.getThreadId());
		}

		if (callAnnot.isReturn()) {
			ateBuilder.setRelevanceInformation(relevanceInfoForInlinedReturn);
			ateBuilder.setStepInfo(StepInfo.PROC_RETURN);
			ateBuilder.setProcedures(callAnnot.getCallStatement().getMethodName(), null);
		} else {
			ateBuilder.setStepInfo(StepInfo.PROC_CALL);
			ateBuilder.setProcedures(null, callAnnot.getCallStatement().getMethodName());
		}
		return Collections.singletonList(ateBuilder.build());
	}

	/**
	 * Creates the set of procedures (more specifically, their identifiers), that where called but didn't return yet.
	 * Note that non-inlined calls aren't included.
	 *
	 * @return Set of unreturned inlined procedures.
	 */
	public Set<String> unreturnedInlinedProcedures() {
		final Set<String> unretInldProcs = new HashSet<>();
		for (final BackTransValue btv : mPrevBackTranslations) {
			for (final CallStatement callStmt : btv.getOriginalCallStack()) {
				unretInldProcs.add(callStmt.getMethodName());
			}
			unretInldProcs.add(btv.getInlineEntryProcId());
		}
		return unretInldProcs;
	}
}
