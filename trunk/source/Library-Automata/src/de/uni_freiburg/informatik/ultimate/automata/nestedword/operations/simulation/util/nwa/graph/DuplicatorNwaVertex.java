/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2009-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.TransitionType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.IGameLetter;

/**
 * A vertex representing that its <i>Duplicator</i>s turn in the game defined by a
 * {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.AGameGraph AGameGraph}.<br/>
 * <br/>
 * The vertex representation is <b>(q0, q1, a, bit)</b> which means <i>Spoiler</i> is currently at state q0 and made a
 * move using an a-transition before whereas <i>Duplicator</i> now is at q1 and must try to also use an a-transition.
 * The bit encodes extra information if needed. This object extends regular DuplicatorVertices by giving it extra
 * information that only occur in Nwa Game Graphs, like sinks.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * @param <LETTER>
 *            Letter class of nwa automaton
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class DuplicatorNwaVertex<LETTER, STATE> extends DuplicatorVertex<LETTER, STATE>
		implements IGameLetter<LETTER, STATE> {

	/**
	 * The sink this vertex belongs to if it is generated as a shadow vertex for such, <tt>null</tt> if not set.
	 */
	private final IWinningSink<LETTER, STATE> mSink;
	/**
	 * The summarize edge this vertex belongs to if it is generated as a shadow vertex for such, <tt>null</tt> if not
	 * set.
	 */
	private final SummarizeEdge<LETTER, STATE> mSummarizeEdge;
	/**
	 * The type of the transition, i.e. if it stands for an internal, call or return transition.
	 */
	private final TransitionType mTransitionType;

	/**
	 * Constructs a new duplicator vertex with given representation <b>(q0, q1, a, bit)</b> which means <i>Spoiler</i>
	 * is currently at state q0 and made a move using an a-transition before whereas <i>Duplicator</i> now is at q1 and
	 * must try to also use an a-transition. The bit encodes extra information if needed.
	 * 
	 * @param priority
	 *            The priority of the vertex
	 * @param b
	 *            The extra bit of the vertex
	 * @param q0
	 *            The state spoiler is at, interpreted as up state
	 * @param q1
	 *            The state duplicator is at, interpreted as up state
	 * @param a
	 *            The letter spoiler used before
	 * @param transitionType
	 *            The type of the transition, i.e. if it stands for an internal, call or return transition
	 */
	public DuplicatorNwaVertex(final int priority, final boolean b, final STATE q0, final STATE q1, final LETTER a,
			final TransitionType transitionType) {
		this(priority, b, q0, q1, a, transitionType, null, null);
	}

	/**
	 * Constructs a new duplicator vertex with given representation <b>(q0, q1, a, bit)</b> which means <i>Spoiler</i>
	 * is currently at state q0 and made a move using an a-transition before whereas <i>Duplicator</i> now is at q1 and
	 * must try to also use an a-transition. The bit encodes extra information if needed. If the used transition is of
	 * type {@link TransitionType#SINK} one can set <tt>sink</tt> to distinguish between similar sinks.
	 * 
	 * @param priority
	 *            The priority of the vertex
	 * @param b
	 *            The extra bit of the vertex
	 * @param q0
	 *            The state spoiler is at, interpreted as up state
	 * @param q1
	 *            The state duplicator is at, interpreted as up state
	 * @param a
	 *            The letter spoiler used before
	 * @param transitionType
	 *            The type of the transition, i.e. if it stands for an internal, call or return transition
	 * @param sink
	 *            The sink this vertex belongs to if it is generated as a shadow vertex for such.
	 */
	public DuplicatorNwaVertex(final int priority, final boolean b, final STATE q0, final STATE q1, final LETTER a,
			final TransitionType transitionType, final IWinningSink<LETTER, STATE> sink) {
		this(priority, b, q0, q1, a, transitionType, null, sink);
	}

	/**
	 * Constructs a new duplicator vertex with given representation <b>(q0, q1, a, bit)</b> which means <i>Spoiler</i>
	 * is currently at state q0 and made a move using an a-transition before whereas <i>Duplicator</i> now is at q1 and
	 * must try to also use an a-transition. The bit encodes extra information if needed. If the used transition is of
	 * type {@link TransitionType#SUMMARIZE_ENTRY} or {@link TransitionType#SUMMARIZE_EXIT} one can set
	 * <tt>summarizeEdge</tt> to distinguish between similar summarize edges.
	 * 
	 * @param priority
	 *            The priority of the vertex
	 * @param b
	 *            The extra bit of the vertex
	 * @param q0
	 *            The state spoiler is at, interpreted as up state
	 * @param q1
	 *            The state duplicator is at, interpreted as up state
	 * @param a
	 *            The letter spoiler used before
	 * @param transitionType
	 *            The type of the transition, i.e. if it stands for an internal, call or return transition
	 * @param summarizeEdge
	 *            The summarize edge this vertex belongs to if it is generated as a shadow vertex.
	 */
	public DuplicatorNwaVertex(final int priority, final boolean b, final STATE q0, final STATE q1, final LETTER a,
			final TransitionType transitionType, final SummarizeEdge<LETTER, STATE> summarizeEdge) {
		this(priority, b, q0, q1, a, transitionType, summarizeEdge, null);
	}

	/**
	 * Constructs a new duplicator vertex with given representation <b>(q0, q1, a, bit)</b> which means <i>Spoiler</i>
	 * is currently at state q0 and made a move using an a-transition before whereas <i>Duplicator</i> now is at q1 and
	 * must try to also use an a-transition. The bit encodes extra information if needed. If the used transition is of
	 * type {@link TransitionType#SUMMARIZE_ENTRY} or {@link TransitionType#SUMMARIZE_EXIT} one can set
	 * <tt>summarizeEdge</tt> to distinguish between similar summarize edges. If the used transition is of type
	 * {@link TransitionType#SINK} one can set <tt>sink</tt> to distinguish between similar sinks.
	 * 
	 * @param priority
	 *            The priority of the vertex
	 * @param b
	 *            The extra bit of the vertex
	 * @param q0
	 *            The state spoiler is at, interpreted as up state
	 * @param q1
	 *            The state duplicator is at, interpreted as up state
	 * @param a
	 *            The letter spoiler used before
	 * @param transitionType
	 *            The type of the transition, i.e. if it stands for an internal, call or return transition
	 * @param summarizeEdge
	 *            The summarize edge this vertex belongs to if it is generated as a shadow vertex for such.
	 * @param sink
	 *            The sink this vertex belongs to if it is generated as a shadow vertex for such.
	 */
	private DuplicatorNwaVertex(final int priority, final boolean b, final STATE q0, final STATE q1, final LETTER a,
			final TransitionType transitionType, final SummarizeEdge<LETTER, STATE> summarizeEdge,
			final IWinningSink<LETTER, STATE> sink) {
		super(priority, b, q0, q1, a);
		mTransitionType = transitionType;
		mSummarizeEdge = summarizeEdge;
		mSink = sink;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (!super.equals(obj)) {
			return false;
		}
		if (!(obj instanceof DuplicatorNwaVertex)) {
			return false;
		}
		final DuplicatorNwaVertex<?, ?> other = (DuplicatorNwaVertex<?, ?>) obj;
		if (mSink == null) {
			if (other.mSink != null) {
				return false;
			}
		} else if (!mSink.equals(other.mSink)) {
			return false;
		}
		if (mSummarizeEdge == null) {
			if (other.mSummarizeEdge != null) {
				return false;
			}
		} else if (!mSummarizeEdge.equals(other.mSummarizeEdge)) {
			return false;
		}
		return mTransitionType == other.mTransitionType;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.vertices.Vertex#getName()
	 */
	@Override
	public String getName() {
		final StringBuilder sb = new StringBuilder();
		sb.append(isB() + "," + getQ0() + "," + getQ1() + ",");
		if (mTransitionType.equals(TransitionType.SUMMARIZE_ENTRY)) {
			sb.append("SEntry/").append(mSummarizeEdge.hashCode());
		} else if (mTransitionType.equals(TransitionType.SUMMARIZE_EXIT)) {
			sb.append("SExit/").append(mSummarizeEdge.hashCode());
		} else if (mTransitionType.equals(TransitionType.SINK)) {
			sb.append("Sink/").append(mSink.hashCode());
		} else {
			sb.append(getLetter());
		}
		sb.append("<" + getPriority() + ">");
		return sb.toString();
	}

	/**
	 * Gets the sink this vertex belongs to or <tt>null</tt> if not set. This field should only be used if the type of
	 * the used transition is {@link TransitionType#SINK}.
	 * 
	 * @return The summarize edge this vertex belongs to or <tt>null</tt> if not set.
	 */
	public IWinningSink<LETTER, STATE> getSink() {
		return mSink;
	}

	/**
	 * Gets the summarize edge this vertex belongs to or <tt>null</tt> if not set. This field should only be used if the
	 * type of the used transition is {@link TransitionType#SUMMARIZE_ENTRY} or {@link TransitionType#SUMMARIZE_EXIT}.
	 * 
	 * @return The summarize edge this vertex belongs to or <tt>null</tt> if not set.
	 */
	public SummarizeEdge<LETTER, STATE> getSummarizeEdge() {
		return mSummarizeEdge;
	}

	/**
	 * Gets the type of the transition represented by this vertex.
	 * 
	 * @return The type of the transition represented by this vertex.
	 */
	@Override
	public TransitionType getTransitionType() {
		return mTransitionType;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + ((mSink == null) ? 0 : mSink.hashCode());
		result = prime * result + ((mSummarizeEdge == null) ? 0 : mSummarizeEdge.hashCode());
		result = prime * result + ((mTransitionType == null) ? 0 : mTransitionType.hashCode());
		return result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("<").append(isB()).append(",(").append(getQ0()).append(",");
		sb.append(getQ1()).append(",");
		if (mTransitionType.equals(TransitionType.SUMMARIZE_ENTRY)) {
			sb.append("SEntry/").append(mSummarizeEdge.hashCode());
		} else if (mTransitionType.equals(TransitionType.SUMMARIZE_EXIT)) {
			sb.append("SExit/").append(mSummarizeEdge.hashCode());
		} else if (mTransitionType.equals(TransitionType.SINK)) {
			sb.append("Sink/").append(mSink.hashCode());
		} else {
			sb.append(getLetter());
		}
		sb.append("),p:").append(getPriority()).append(",pm:").append(mPm);
		sb.append(">");
		return sb.toString();
	}
}
