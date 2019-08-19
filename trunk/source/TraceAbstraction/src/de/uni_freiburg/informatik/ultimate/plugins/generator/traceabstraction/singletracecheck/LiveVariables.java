/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashSet;

/**
 * Compute the live variables along a trace. Use data structures from the SSA construction for this computation.
 * Position i in the list of live variables refers to the position between CodeBlock i-1 and CodeBlock i in the trace.
 * Position 0 in the list of live variables refers to the precondition, Position trace.length+1 refers to the
 * postcondition. A variable is live at position i if it is used in a CodeBlock with position <i and it is used in a
 * CodeBlock with position >= i and if it belongs to the current calling context. We have the following definition of
 * used: A variable is used in a CodeBlock, if it occurs in the code block. If g is a global variable that is modified
 * by procedure proc, the the variables g and old(g) are used in each call to proc and in each return from proc.
 * Furthermore each global variable (even if not modified) that occur in a procedure (along this trace) is used at the
 * return of this procedure.
 * 
 * @author musab@informatik.uni-freiburg.de, heizmann@informatik.uni-freiburg.de
 *
 */
public class LiveVariables {
	private final Map<Term, IProgramVar> mConstants2BoogieVar;
	private final ModifiableNestedFormulas<Map<Term, Term>, Map<Term, Term>> mTraceWithConstants;
	private final Map<IProgramVar, TreeMap<Integer, Term>> mIndexedVarRepresentative;

	private final Collection<Term>[] mConstantsForEachPosition;
	private final Set<Term>[] mLiveConstants;
	// mLiveVariables[i] are the live variables _before_ statement i
	private final Set<IProgramVar>[] mLiveVariables;

	public LiveVariables(final ModifiableNestedFormulas<Map<Term, Term>, Map<Term, Term>> traceWithConstants,
			final Map<Term, IProgramVar> constants2BoogieVar,
			final Map<IProgramVar, TreeMap<Integer, Term>> indexedVarRepresentative) {
		mConstants2BoogieVar = constants2BoogieVar;
		mTraceWithConstants = traceWithConstants;
		mIndexedVarRepresentative = indexedVarRepresentative;
		// We compute constants for each position of trace, the precondition
		// and the postcondition.
		mConstantsForEachPosition = fetchConstantsForEachPosition();
		mLiveConstants = computeLiveConstants();
		mLiveVariables = computeLiveVariables();
	}

	/**
	 * Fetch all constants (which are indexed instances of a variable in the SSA) that represent BoogieVars for the
	 * precondition, for each CodeBlock of the trace and for the post-condition. Returns an array of length
	 * (trace.length + 2) such that
	 * <ul>
	 * <li>at pos = 0, there are the constants of the precondition
	 * <li>at pos = trace.length + 1, there are the constants of the postcondition
	 * <li>at pos = i+1 there are the constants for the CodeBlocks of the trace at position i.
	 * </ul>
	 * The assignment of TransFormulas to positions is the same as for the computation of nested interpolants:
	 * <ul>
	 * <li>if i is an internal position we use the formula from this position
	 * <li>if i is the position of a pending call, we use the localVarAssignment, the globalVarAssignment and the
	 * OldVarAssignment,
	 * <li>if i is the position of a non-pending call, we use the globalVarAssignment
	 * <li>if i is a return position, we use the formula of the return position, the localVarAssignment and the
	 * oldVarAssignment
	 * </ul>
	 * 
	 */
	private Collection<Term>[] fetchConstantsForEachPosition() {
		@SuppressWarnings("unchecked")
		final Collection<Term>[] result = new Collection[mTraceWithConstants.getTrace().length() + 2];
		// Add constants for the precondition
		result[0] = extractVarConstants(mTraceWithConstants.getPrecondition().values());
		// add constants for the post-condition
		final int lastPosition = mTraceWithConstants.getTrace().length() + 1;
		result[lastPosition] = extractVarConstants(mTraceWithConstants.getPostcondition().values());
		for (int i = 0; i < mTraceWithConstants.getTrace().length(); i++) {
			if (mTraceWithConstants.getTrace().isCallPosition(i)) {
				assert result[i + 1] == null : "constants for position " + (i + 1) + " already fetched!";
				if (mTraceWithConstants.getTrace().isPendingCall(i)) {
					result[i + 1] = extractVarConstants(mTraceWithConstants.getLocalVarAssignment(i).values(),
							mTraceWithConstants.getGlobalVarAssignment(i).values(),
							mTraceWithConstants.getOldVarAssignment(i).values());
				} else {
					result[i + 1] = extractVarConstants(mTraceWithConstants.getGlobalVarAssignment(i).values());
				}
			} else if (mTraceWithConstants.getTrace().isReturnPosition(i)) {
				assert result[i + 1] == null : "constants for position " + (i + 1) + " already fetched!";
				if (mTraceWithConstants.getTrace().isPendingReturn(i)) {
					throw new AssertionError("not yet implemented");
				}
				final int call_pos = mTraceWithConstants.getTrace().getCallPosition(i);
				result[i + 1] = extractVarConstants(mTraceWithConstants.getFormulaFromNonCallPos(i).values(),
						mTraceWithConstants.getLocalVarAssignment(call_pos).values(),
						mTraceWithConstants.getOldVarAssignment(call_pos).values());
			} else {
				assert result[i + 1] == null : "constants for position " + (i + 1) + " already fetched!";
				assert mTraceWithConstants.getTrace().isInternalPosition(i);
				result[i + 1] = extractVarConstants(mTraceWithConstants.getFormulaFromNonCallPos(i).values());
			}
		}
		return result;
	}

	/**
	 * Returns a set that contains all terms from collections that represent a BoogieVar. (used to filter out constants
	 * that only correspond to auxVars)
	 */
	@SafeVarargs
	private final Set<Term> extractVarConstants(final Collection<Term>... collections) {
		final Set<Term> result = new HashSet<>();
		for (final Collection<Term> terms : collections) {
			for (final Term term : terms) {
				if (mConstants2BoogieVar.containsKey(term)) {
					// constant represents a BoogieVar
					result.add(term);
				}
			}
		}
		return result;
	}

	/**
	 * Compute at which position of the trace which constant is live. Returns an array of length (trace.length + 1)
	 * where the position i refers to the position between CodeBlock i-1 and CodeBlock i. Furthermore position 0 refers
	 * to the precondition and position trace.length + 1 refers to the postcondition. A constant is live at position i
	 * if it is used in a CodeBlock with position <i and it is used in a CodeBlock with position >= i and if it belongs
	 * to the current calling context.
	 */
	private Set<Term>[] computeLiveConstants() {
		// Idea of this algorithm:
		// - traverse the trace backwards
		// - add all constants that occur
		// - remove all constants that have the index of the current position
		// (because they occur here for the first time and are not contained
		// in a prefix of the trace)
		// - take care for contexts, calls returns
		@SuppressWarnings("unchecked")
		final Set<Term>[] result = new Set[mTraceWithConstants.getTrace().length() + 1];
		{
			final HashSet<Term> liveConstants = new HashSet<>(mConstantsForEachPosition[result.length]);
			removeConstantsWithIndex_i(liveConstants, result.length - 1);
			result[result.length - 1] = liveConstants;
		}
		for (int i = result.length - 2; i >= 0; i--) {
			final HashSet<Term> liveConstants = new HashSet<>();
			if (mTraceWithConstants.getTrace().isCallPosition(i)) {
				final String caller = mTraceWithConstants.getTrace().getSymbol(i).getPrecedingProcedure();
				if (mTraceWithConstants.getTrace().isPendingCall(i)) {
					addGlobals(liveConstants, result[i + 1]);
					addGlobals(liveConstants, mConstantsForEachPosition[i + 1]);
					addLocals(caller, liveConstants, mConstantsForEachPosition[i + 1]);
				} else {
					final int returnPos = mTraceWithConstants.getTrace().getReturnPosition(i);
					addLocals(caller, liveConstants, result[returnPos + 1]);
					addLocals(caller, liveConstants, mConstantsForEachPosition[returnPos + 1]);
					removeConstantsWithIndex_i(liveConstants, returnPos);
					addGlobals(liveConstants, result[i + 1]);
					addGlobals(liveConstants, mConstantsForEachPosition[i + 1]);

				}
			} else if (mTraceWithConstants.getTrace().isReturnPosition(i)) {
				final String callee = mTraceWithConstants.getTrace().getSymbol(i).getPrecedingProcedure();
				addGlobals(liveConstants, result[i + 1]);
				addGlobals(liveConstants, mConstantsForEachPosition[i + 1]);
				addLocals(callee, liveConstants, mConstantsForEachPosition[i + 1]);
			} else {
				assert mTraceWithConstants.getTrace().isInternalPosition(i);
				liveConstants.addAll(mConstantsForEachPosition[i + 1]);
				liveConstants.addAll(result[i + 1]);
			}
			removeConstantsWithIndex_i(liveConstants, i);
			result[i] = liveConstants;
		}
		return result;
	}

	/**
	 * Add to writeSet all constants from readCollection that correspond to global BoogieVars.
	 */
	private void addGlobals(final HashSet<Term> writeSet, final Collection<Term> readCollection) {
		for (final Term term : readCollection) {
			final IProgramVar bv = mConstants2BoogieVar.get(term);
			if (bv.isGlobal()) {
				writeSet.add(term);
			}
		}
	}

	/**
	 * Add to writeSet all constants from readCollection that correspond to local BoogieVars of procedure proc
	 */
	private void addLocals(final String proc, final HashSet<Term> writeSet, final Collection<Term> readCollection) {
		for (final Term term : readCollection) {
			final IProgramVar bv = mConstants2BoogieVar.get(term);
			if (!bv.isGlobal()) {
				if (bv.getProcedure().equals(proc)) {
					writeSet.add(term);
				}
			}
		}
	}

	/**
	 * Remove from set all constants whose index is i.
	 */
	private void removeConstantsWithIndex_i(final HashSet<Term> set, final int i) {
		final Iterator<Term> it = set.iterator();
		while (it.hasNext()) {
			final Term term = it.next();
			final IProgramVar bv = mConstants2BoogieVar.get(term);
			final Map<Integer, Term> indexedVar = mIndexedVarRepresentative.get(bv);
			if (indexedVar.get(i) == term) {
				it.remove();
			}
		}
	}

	/**
	 * Use the live constants to compute live variables. The corresponding BoogieVar of each live constant is a live
	 * variable. Furthermore each global variable that occurs between a call and return is live until the return.
	 */
	private Set<IProgramVar>[] computeLiveVariables() {
		@SuppressWarnings("unchecked")
		final Set<IProgramVar>[] result = new Set[mTraceWithConstants.getTrace().length() + 1];
		final ScopedHashSet<IProgramVar> globalVarsBetweenCallAndReturn = new ScopedHashSet<>();
		for (int i = 0; i < result.length; i++) {
			if (i > 0 && i < result.length - 1 && mTraceWithConstants.getTrace().isCallPosition(i - 1)
					&& !mTraceWithConstants.getTrace().isPendingCall(i - 1)) {
				globalVarsBetweenCallAndReturn.beginScope();
			}
			if (i > 0 && i < result.length - 1 && mTraceWithConstants.getTrace().isReturnPosition(i - 1)) {
				if (mTraceWithConstants.getTrace().isPendingReturn(i - 1)) {
					throw new AssertionError("not yet implemented");
				}
				globalVarsBetweenCallAndReturn.endScope();
			}
			final Set<IProgramVar> liveVars = new HashSet<>();
			for (final Term t : mLiveConstants[i]) {
				final IProgramVar bv = mConstants2BoogieVar.get(t);
				if (!globalVarsBetweenCallAndReturn.isEmptyScope() && bv.isGlobal()) {
					globalVarsBetweenCallAndReturn.add(bv);
				} else {
					liveVars.add(bv);
				}
			}
			liveVars.addAll(globalVarsBetweenCallAndReturn);
			result[i] = liveVars;
		}
		return result;
	}

	public Set<IProgramVar>[] getLiveVariables() {
		return mLiveVariables;
	}
}
