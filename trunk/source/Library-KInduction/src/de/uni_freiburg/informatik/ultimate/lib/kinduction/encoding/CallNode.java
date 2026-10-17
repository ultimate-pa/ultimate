/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE KInduction Library.
 *
 * The ULTIMATE KInduction Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE KInduction Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE KInduction Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE KInduction Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE KInduction Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;

/**
 * A state of the abstraction together with the chain of call sites it was reached through: the node type of the flat
 * graph {@link LoopTreeFormulaBuilder} works on once calls are resolved.
 * <p>
 * The flat graph has no call stack, so a callee that is called from two sites and is not summarized but
 * <em>unfolded</em> must contribute two disjoint copies of its states - otherwise the two call sites look like a
 * loop and a path may enter at one of them and return to the other, splicing away everything in between (see the
 * {@link ProcedureSummaries} class javadoc). The call site chain is what makes those copies distinct: two nodes are
 * equal only if they carry the same state and were reached through the same sequence of call sites.
 * <p>
 * The chain is stored as a link to the <b>call site node</b> in the caller, which is itself a {@code CallNode} and
 * therefore carries the rest of the chain. A node of the procedure the analysis starts in has no such frame.
 * <p>
 * The chain is always finite because nothing on a call cycle is ever unfolded: a recursive procedure's activations
 * are told apart by {@link CallStack} in the state rather than by copies of its states, so its own nodes are
 * {@link #root} nodes and a node reached through one carries only the part of the chain the graph still
 * distinguishes. That is why a node does <b>not</b> determine how many calls are open at it, which
 * {@link KInductionCounterexampleBuilder} has to allow for when it cuts a run into pc steps.
 *
 * <pre>{@code
 * CallNode<STATE> callSite = ...;                  // a state of the caller with an outgoing call transition
 * CallNode<STATE> entry = callSite.enter(e);       // the callee's entry state, one level deeper
 * CallNode<STATE> exit = entry.sibling(x);         // another state of the callee, same frame
 * CallNode<STATE> afterReturn = callSite.sibling(r); // back in the caller, at the return's successor
 * }</pre>
 *
 * Instances are immutable and their hash code is computed once, in the constructor: they are used as map keys
 * throughout the loop tree and the pc transition system.
 *
 * @param <STATE>
 *            state type of the abstraction
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class CallNode<STATE> {

	private final STATE mState;
	/** The call site this node was reached through, or {@code null} for the procedure the analysis starts in. */
	private final CallNode<STATE> mFrame;
	private final int mDepth;
	private final int mHash;

	private CallNode(final STATE state, final CallNode<STATE> frame) {
		mState = Objects.requireNonNull(state);
		mFrame = frame;
		mDepth = frame == null ? 0 : frame.mDepth + 1;
		mHash = 31 * state.hashCode() + (frame == null ? 0 : frame.mHash);
	}

	/** A node of the procedure the analysis starts in, i.e. with no pending call. */
	public static <STATE> CallNode<STATE> root(final STATE state) {
		return new CallNode<>(state, null);
	}

	/**
	 * The callee state {@code calleeState} reached by taking a call at <b>this</b> node, which therefore becomes
	 * the new frame.
	 */
	public CallNode<STATE> enter(final STATE calleeState) {
		return new CallNode<>(calleeState, this);
	}

	/** Another state of the same procedure activation, i.e. with the same call site chain. */
	public CallNode<STATE> sibling(final STATE other) {
		return new CallNode<>(other, mFrame);
	}

	public STATE getState() {
		return mState;
	}

	/** The call site this node was reached through, or {@code null} if no call is pending here. */
	public CallNode<STATE> getFrame() {
		return mFrame;
	}

	/** How many calls are pending at this node. Zero in the procedure the analysis starts in. */
	public int getDepth() {
		return mDepth;
	}

	/**
	 * The states of the pending call sites, innermost first. Empty iff {@link #getDepth()} is zero. This is the
	 * shape {@link KInductionCounterexampleBuilder} keeps its own call stack in, so the two can be compared.
	 */
	public List<STATE> getCallSites() {
		if (mFrame == null) {
			return Collections.emptyList();
		}
		final List<STATE> result = new ArrayList<>(mDepth);
		for (CallNode<STATE> frame = mFrame; frame != null; frame = frame.mFrame) {
			result.add(frame.mState);
		}
		return result;
	}

	@Override
	public int hashCode() {
		return mHash;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (!(obj instanceof CallNode)) {
			return false;
		}
		final CallNode<?> other = (CallNode<?>) obj;
		return mHash == other.mHash && mDepth == other.mDepth && mState.equals(other.mState)
				&& Objects.equals(mFrame, other.mFrame);
	}

	@Override
	public String toString() {
		if (mFrame == null) {
			return String.valueOf(mState);
		}
		return mState + "@" + getCallSites();
	}
}
