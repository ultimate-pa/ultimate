/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.util.Set;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;

/**
 * Class that represents a sequence of formulas (of type F) along a trace (given by a NestedWord<CodeBlock>). At
 * position that is neither a call position nor a pending return position there is one formula. At each call position
 * and each pending return position there are three formulas
 * <ul>
 * <li>one that represents an assignment of certain local variables namely the (input) parameters of the called
 * procedure,
 * <li>one that represents an assignment of all global variables that may be modified by the called procedure, and
 * <li>one that represents an assignment of all oldvars of global variables that may be modified by the called
 * procedure. The class uses assertions to check that indices for all public getters of this class are valid. Subclasses
 * have to override the methods with the <i>FromValidPos</i> suffix and may assume that validity of the index was
 * checked (in case assertions are enabled)
 *
 * @author Matthias Heizmann
 *
 * @param <TF>
 *            Type of the formulas along the trace.
 */
public abstract class NestedFormulas<TF, SF> {

	private final NestedWord<? extends IAction> mNestedWord;
	private SF mPrecondition;
	private SF mPostcondition;
	private final SortedMap<Integer, SF> mPendingContexts;

	public NestedFormulas(final NestedWord<? extends IAction> nestedWord,
			final SortedMap<Integer, SF> pendingContexts) {
		mNestedWord = nestedWord;
		assert pendingContexts != null;
		mPendingContexts = pendingContexts;
	}

	public final NestedWord<? extends IAction> getTrace() {
		return mNestedWord;
	}

	public final SF getPrecondition() {
		return mPrecondition;
	}

	public void setPrecondition(final SF sf) {
		assert mPrecondition == null : "already set";
		mPrecondition = sf;
	}

	public final SF getPostcondition() {
		return mPostcondition;
	}

	public void setPostcondition(final SF sf) {
		assert mPostcondition == null : "already set";
		mPostcondition = sf;
	}

	public SF getPendingContext(final int i) {
		assert mNestedWord.isPendingReturn(i) : "no pending return";
		return mPendingContexts.get(i);
	}

	public void setPendingContext(final int i, final SF sf) {
		assert !mPendingContexts.containsKey(i) : "already set";
		assert mNestedWord.isPendingReturn(i) : "no pending return";
		mPendingContexts.put(i, sf);
	}

	public final Set<Integer> callPositions() {
		return mNestedWord.getCallPositions();
	}

	public final TF getFormulaFromNonCallPos(final int i) {
		assert i >= 0 && i < mNestedWord.length() : "out of range";
		assert !mNestedWord.isCallPosition(i) : "call position";
		return getFormulaFromValidNonCallPos(i);
	}

	protected abstract TF getFormulaFromValidNonCallPos(int i);

	public TF getLocalVarAssignment(final int i) {
		assert i >= 0 && i < mNestedWord.length() : "out of range";
		assert callPositions().contains(i)
				|| mNestedWord.isPendingReturn(i) : "neither call nor pending return position";
		assert mNestedWord.isCallPosition(i)
				|| mNestedWord.isPendingReturn(i) : "neither call nor pending return position";
		return getLocalVarAssignmentFromValidPos(i);
	}

	protected abstract TF getLocalVarAssignmentFromValidPos(int i);

	public TF getGlobalVarAssignment(final int i) {
		assert i >= 0 && i < mNestedWord.length() : "out of range";
		assert callPositions().contains(i) : "no call position";
		assert mNestedWord.isCallPosition(i) : "no call position";
		return getGlobalVarAssignmentFromValidPos(i);
	}

	protected abstract TF getGlobalVarAssignmentFromValidPos(int i);

	public TF getOldVarAssignment(final int i) {
		assert i >= 0 && i < mNestedWord.length() : "out of range";
		assert callPositions().contains(i)
				|| mNestedWord.isPendingReturn(i) : "neither call nor pending return position";
		assert mNestedWord.isCallPosition(i)
				|| mNestedWord.isPendingReturn(i) : "neither call nor pending return position";
		return getOldVarAssignmentFromValidPos(i);
	}

	protected abstract TF getOldVarAssignmentFromValidPos(int i);

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		for (int i=0; i<mNestedWord.length(); i++) {
			sb.append("Position " + i + ": ");
			sb.append(String.valueOf(mNestedWord.getSymbol(i).getTransformula()));
			sb.append(System.lineSeparator());
		}
		return sb.toString();
	}

}
