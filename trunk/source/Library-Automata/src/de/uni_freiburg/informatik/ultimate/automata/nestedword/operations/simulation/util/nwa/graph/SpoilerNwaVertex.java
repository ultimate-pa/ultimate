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

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.SpoilerVertex;

/**
 * A vertex representing that its <i>Spoiler</i>s turn in the game defined by a
 * {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.AGameGraph
 * AGameGraph}.<br/>
 * <br/>
 * 
 * The vertex representation is <b>(q0, q1, bit)</b> which means <i>Spoiler</i>
 * is currently at state q0 and must make a move using an arbitrary transition
 * whereas <i>Duplicator</i> now is at q1 and later must respond to
 * <i>Spoiler</i>s decision. The bit encodes extra information if needed.
 * 
 * This object extends regular SpoilerVertices by giving it extra information
 * that only occur in Nwa Game Graphs, like sinks.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * 
 * @param <LETTER>
 *            Letter class of nwa automaton
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class SpoilerNwaVertex<LETTER, STATE> extends SpoilerVertex<LETTER, STATE> {

	/**
	 * The sink this vertex belongs to if it is generated as a shadow vertex for
	 * such, <tt>null</tt> if not set.
	 */
	private final IWinningSink<LETTER, STATE> mSink;
	/**
	 * The summarize edge this vertex belongs to if it is generated as a shadow
	 * vertex for such, <tt>null</tt> if not set.
	 */
	private final SummarizeEdge<LETTER, STATE> mSummarizeEdge;

	/**
	 * Constructs a new spoiler vertex with given representation <b>(q0, q1,
	 * bit)</b> which means <i>Spoiler</i> is currently at state q0 and must
	 * make a move using an arbitrary transition whereas <i>Duplicator</i> now
	 * is at q1 and later must respond to <i>Spoiler</i>s decision. The bit
	 * encodes extra information if needed.
	 * 
	 * @param priority
	 *            The priority of the vertex
	 * @param b
	 *            The extra bit of the vertex
	 * @param q0
	 *            The state spoiler is at, interpreted as up state
	 * @param q1
	 *            The state duplicator is at, interpreted as up state
	 */
	public SpoilerNwaVertex(final int priority, final boolean b, final STATE q0, final STATE q1) {
		this(priority, b, q0, q1, null, null);
	}

	/**
	 * Constructs a new spoiler vertex with given representation <b>(q0, q1,
	 * bit)</b> which means <i>Spoiler</i> is currently at state q0 and must
	 * make a move using an arbitrary transition whereas <i>Duplicator</i> now
	 * is at q1 and later must respond to <i>Spoiler</i>s decision. The bit
	 * encodes extra information if needed.
	 * 
	 * @param priority
	 *            The priority of the vertex
	 * @param b
	 *            The extra bit of the vertex
	 * @param q0
	 *            The state spoiler is at, interpreted as up state
	 * @param q1
	 *            The state duplicator is at, interpreted as up state
	 * @param sink
	 *            The sink this vertex belongs to if it is generated as a shadow
	 *            vertex for such.
	 */
	public SpoilerNwaVertex(final int priority, final boolean b, final STATE q0, final STATE q1,
			final IWinningSink<LETTER, STATE> sink) {
		this(priority, b, q0, q1, null, sink);
	}

	/**
	 * Constructs a new spoiler vertex with given representation <b>(q0, q1,
	 * bit)</b> which means <i>Spoiler</i> is currently at state q0 and must
	 * make a move using an arbitrary transition whereas <i>Duplicator</i> now
	 * is at q1 and later must respond to <i>Spoiler</i>s decision. The bit
	 * encodes extra information if needed.
	 * 
	 * @param priority
	 *            The priority of the vertex
	 * @param b
	 *            The extra bit of the vertex
	 * @param q0
	 *            The state spoiler is at, interpreted as up state
	 * @param q1
	 *            The state duplicator is at, interpreted as up state
	 * @param summarizeEdge
	 *            The summarize edge this vertex belongs to if it is generated
	 *            as a shadow vertex.
	 */
	public SpoilerNwaVertex(final int priority, final boolean b, final STATE q0, final STATE q1,
			final SummarizeEdge<LETTER, STATE> summarizeEdge) {
		this(priority, b, q0, q1, summarizeEdge, null);
	}

	/**
	 * Constructs a new spoiler vertex with given representation <b>(q0, q1,
	 * bit)</b> which means <i>Spoiler</i> is currently at state q0 and must
	 * make a move using an arbitrary transition whereas <i>Duplicator</i> now
	 * is at q1 and later must respond to <i>Spoiler</i>s decision. The bit
	 * encodes extra information if needed.
	 * 
	 * @param priority
	 *            The priority of the vertex
	 * @param b
	 *            The extra bit of the vertex
	 * @param q0
	 *            The state spoiler is at, interpreted as up state
	 * @param q1
	 *            The state duplicator is at, interpreted as up state
	 * @param summarizeEdge
	 *            The summarize edge this vertex belongs to if it is generated
	 *            as a shadow vertex.
	 * @param sink
	 *            The sink this vertex belongs to if it is generated as a shadow
	 *            vertex for such.
	 */
	private SpoilerNwaVertex(final int priority, final boolean b, final STATE q0, final STATE q1,
			final SummarizeEdge<LETTER, STATE> summarizeEdge, final IWinningSink<LETTER, STATE> sink) {
		super(priority, b, q0, q1);
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
		if (!(obj instanceof SpoilerNwaVertex)) {
			return false;
		}
		final SpoilerNwaVertex<?, ?> other = (SpoilerNwaVertex<?, ?>) obj;
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
		return true;
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
		sb.append(isB() + "," + getQ0() + "," + getQ1());
		if (mSummarizeEdge != null) {
			sb.append("[SMiddle/").append(mSummarizeEdge.hashCode() + "]");
		}
		if (mSink != null) {
			sb.append("[Sink/").append(mSink.hashCode() + "]");
		}
		sb.append("<" + getPriority() + ">");
		return sb.toString();
	}

	/**
	 * Gets the sink this vertex belongs to or <tt>null</tt> if not set.
	 * 
	 * @return The sink this vertex belongs to or <tt>null</tt> if not set.
	 */
	public IWinningSink<LETTER, STATE> getSink() {
		return mSink;
	}

	/**
	 * Gets the summarize edge this vertex belongs to or <tt>null</tt> if not
	 * set.
	 * 
	 * @return The summarize edge this vertex belongs to or <tt>null</tt> if not
	 *         set.
	 */
	public SummarizeEdge<LETTER, STATE> getSummarizeEdge() {
		return mSummarizeEdge;
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
		sb.append(getQ1());
		if (mSummarizeEdge != null) {
			sb.append("[SMiddle/").append(mSummarizeEdge.hashCode() + "]");
		}
		if (mSink != null) {
			sb.append("[Sink/").append(mSink.hashCode() + "]");
		}
		sb.append("),p:").append(getPriority()).append(",pm:").append(mPm);
		sb.append(">");
		return sb.toString();
	}
}
