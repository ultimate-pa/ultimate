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

import java.util.HashMap;
import java.util.Map;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;

/**
 * NestedFormulas where we can set formulas after construction of the object.
 *
 * @author Matthias Heizmann
 *
 * @param <TF>
 *            formula for transitions
 * @param <SF>
 *            formula for states
 */
public class ModifiableNestedFormulas<TF, SF> extends NestedFormulas<TF, SF> {

	/**
	 * If index i is an internal position or a return transition in the nested trace Term[i] represents the i-th
	 * statement. If index i is a call position Term[i] represents the assignment
	 * {@code g_1,...,g_n := old(g_1),...,old(g_n)} where g_1,...,g_n are the global variables modified by the called
	 * procedure.
	 */
	private final TF[] mTerms;

	/**
	 * Maps a call position to a formula that represents the assignment {@code x_1,...,x_n := t_1,...,t_n} where
	 * x_1,...,x_n are the parameters of the callee and t_1,...,t_n are the arguments of the caller.
	 */
	private final Map<Integer, TF> mLocalVarAssignmentAtCall = new HashMap<>();

	/**
	 * Maps a call position to a formula that represents the assignment {@code old(g_1),...,old(g_n) := g_1,...,g_n}
	 * where g_1,...,g_n are the global variables modified by the called procedure.
	 */
	private final Map<Integer, TF> mGlobalOldVarAssignmentAtCall = new HashMap<>();

	public ModifiableNestedFormulas(final NestedWord<? extends IAction> nestedWord,
			final SortedMap<Integer, SF> pendingContexts) {
		super(nestedWord, pendingContexts);
		mTerms = (TF[]) new Object[nestedWord.length()];
	}

	@Override
	protected TF getFormulaFromValidNonCallPos(final int i) {
		return mTerms[i];
	}

	@Override
	protected TF getLocalVarAssignmentFromValidPos(final int i) {
		return mLocalVarAssignmentAtCall.get(i);
	}

	@Override
	protected TF getGlobalVarAssignmentFromValidPos(final int i) {
		return mTerms[i];
	}

	@Override
	protected TF getOldVarAssignmentFromValidPos(final int i) {
		return mGlobalOldVarAssignmentAtCall.get(i);
	}

	void setFormulaAtNonCallPos(final int i, final TF tf) {
		assert !super.getTrace().isCallPosition(i);
		assert mTerms[i] == null : "already set";
		mTerms[i] = tf;
	}

	void setLocalVarAssignmentAtPos(final int i, final TF tf) {
		assert super.getTrace().isCallPosition(i) || super.getTrace().isPendingReturn(i);
		assert mLocalVarAssignmentAtCall.get(i) == null : "already set";
		mLocalVarAssignmentAtCall.put(i, tf);
	}

	void setOldVarAssignmentAtPos(final int i, final TF tf) {
		assert super.getTrace().isCallPosition(i) || super.getTrace().isPendingReturn(i);
		assert mGlobalOldVarAssignmentAtCall.get(i) == null : "already set";
		mGlobalOldVarAssignmentAtCall.put(i, tf);
	}

	void setGlobalVarAssignmentAtPos(final int i, final TF tf) {
		assert super.getTrace().isCallPosition(i) || super.getTrace().isPendingReturn(i);
		assert mTerms[i] == null : "already set";
		mTerms[i] = tf;
	}

}
