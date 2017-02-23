/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util;

import java.util.Set;

/**
 * A vertex base class for the game defined by a
 * {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.AGameGraph
 * AGameGraph}.<br/>
 * <br/>
 * The vertex representation is <b>(q0, q1, bit)</b> which means <i>Spoiler</i>
 * is currently at state q0 whereas <i>Duplicator</i> now is at q1. The bit
 * encodes extra information if needed.<br/>
 * A vertex also holds several fields used for simulation calculation, for more
 * information see
 * {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ASimulation
 * ASimulation}.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public class Vertex<LETTER, STATE> {
	/**
	 * The bit encodes extra information if needed.
	 */
	private final boolean mB;
	/**
	 * The best neighbor measure of this vertex as needed for the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ASimulation
	 * ASimulation}.
	 */
	private int mBEff;
	/**
	 * The neighbor counter of this vertex as needed for the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ASimulation
	 * ASimulation}.
	 */
	private int mC;
	/**
	 * Whether this vertex is in the working list of the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ASimulation
	 * ASimulation} or not.
	 */
	private boolean mInWL;
	/**
	 * The priority of this vertex as needed for the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ASimulation
	 * ASimulation}.
	 */
	private int mPriority;
	/**
	 * The label of the first buechi automaton state where <i>Spoiler</i>
	 * currently is at.
	 */
	private final STATE mQ0;
	/**
	 * The label of the second buechi automaton state where <i>Duplicator</i>
	 * currently is at.
	 */
	private final STATE mQ1;
	/**
	 * The progress measure of this vertex as needed for the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ASimulation
	 * ASimulation}.
	 */
	protected int mPm;

	/**
	 * Constructs a new vertex with given representation <b>(q0, q1, bit)</b>
	 * which means <i>Spoiler</i> is currently at state q0 whereas
	 * <i>Duplicator</i> now is at q1. The bit encodes extra information if
	 * needed.
	 * 
	 * @param priority
	 *            The priority of the vertex
	 * @param b
	 *            The extra bit of the vertex
	 * @param q0
	 *            The state spoiler is at
	 * @param q1
	 *            The state duplicator is at
	 */
	public Vertex(final int priority, final boolean b, final STATE q0, final STATE q1) {
		this.mQ0 = q0;
		this.mQ1 = q1;
		this.mB = b;
		this.mPriority = priority;
		this.mPm = 0;
		this.mBEff = 0;
		this.mC = 0;
		this.setInWL(false);
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
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final Vertex<?, ?> other = (Vertex<?, ?>) obj;
		if (mB != other.mB) {
			return false;
		}
		if (mQ0 == null) {
			if (other.mQ0 != null) {
				return false;
			}
		} else if (!mQ0.equals(other.mQ0)) {
			return false;
		}
		if (mQ1 == null) {
			if (other.mQ1 != null) {
				return false;
			}
		} else if (!mQ1.equals(other.mQ1)) {
			return false;
		}
		return true;
	}

	/**
	 * Gets the best neighbor measure of this vertex as needed for the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ASimulation
	 * ASimulation}.
	 * 
	 * @return The best neighbor measure of this vertex
	 */
	public int getBEff() {
		return mBEff;
	}

	/**
	 * Gets the neighbor counter of this vertex as needed for the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ASimulation
	 * ASimulation}.
	 * 
	 * @return The neighbor counter of this vertex
	 */
	public int getC() {
		return mC;
	}

	/**
	 * Gets a human readable name of the object. For example: "q0, q1" or
	 * "q0, q1, a".
	 * 
	 * @return A human readable name of the object
	 */
	public String getName() {
		return toString();
	}

	/**
	 * Gets the progress measure of this vertex as needed for the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ASimulation
	 * ASimulation}.
	 * 
	 * @param scc
	 *            The SCC currently working from
	 * @param infinity
	 *            The currently known upper bound for infinity, for more
	 *            information see
	 *            {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.AGameGraph#getGlobalInfinity()
	 *            AGameGraph.getGlobalInfinity()}.
	 * @return The progress measure of this vertex or 0 if the SCC is not
	 *         <tt>null</tt> and not contains this vertex
	 */
	public int getPM(final Set<Vertex<LETTER, STATE>> scc, final int infinity) {
		if (scc == null) {
			return mPm;
		} else if (mPm == infinity) {
			return infinity;
		} else if (scc.contains(this)) {
			return mPm;
		} else {
			return 0;
		}
	}

	/**
	 * Gets the priority of the vertex.
	 * 
	 * @return The priority
	 */
	public int getPriority() {
		return mPriority;
	}

	/**
	 * Gets the label of the first buechi automaton state where <i>Spoiler</i>
	 * currently is at.
	 * 
	 * @return The label of the first buechi automaton state where
	 *         <i>Spoiler</i> currently is at.
	 */
	public STATE getQ0() {
		return mQ0;
	}

	/**
	 * Gets the label of the second buechi automaton state where
	 * <i>Duplicator</i> currently is at.
	 * 
	 * @return The label of the second buechi automaton state where
	 *         <i>Duplicator</i> currently is at.
	 */
	public STATE getQ1() {
		return mQ1;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (mB ? 1231 : 1237);
		result = prime * result + ((mQ0 == null) ? 0 : mQ0.hashCode());
		result = prime * result + ((mQ1 == null) ? 0 : mQ1.hashCode());
		return result;
	}

	/**
	 * Returns the bit which encodes extra information if needed.
	 * 
	 * @return True if the bit which encodes extra information if needed is
	 *         true, false if not.
	 */
	public boolean isB() {
		return mB;
	}

	/**
	 * Returns if the vertex is an instance of a {@link DuplicatorVertex}.
	 * 
	 * @return True if the vertex is an instance of a {@link DuplicatorVertex},
	 *         false if not.
	 */
	public boolean isDuplicatorVertex() {
		return this instanceof DuplicatorVertex;
	}

	/**
	 * Returns whether this vertex is in the working list of the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ASimulation
	 * ASimulation} or not.
	 * 
	 * @return True if this vertex is in the working list, false if not.
	 */
	public boolean isInWL() {
		return mInWL;
	}

	/**
	 * Returns if the vertex is an instance of a {@link SpoilerVertex}.
	 * 
	 * @return True if the vertex is an instance of a {@link SpoilerVertex},
	 *         false if not.
	 */
	public boolean isSpoilerVertex() {
		return !(this instanceof DuplicatorVertex);
	}

	/**
	 * Sets the best neighbor measure of this vertex as needed for the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ASimulation
	 * ASimulation}.
	 * 
	 * @param b
	 *            The best neighbor measure to set
	 */
	public void setBEff(final int b) {
		this.mBEff = b;
	}

	/**
	 * Sets the neighbor counter of this vertex as needed for the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ASimulation
	 * ASimulation}.
	 * 
	 * @param c
	 *            The neighbor counter to set
	 */
	public void setC(final int c) {
		this.mC = c;
	}

	/**
	 * Sets whether this vertex is in the working list of the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ASimulation
	 * ASimulation} or not.
	 * 
	 * @param inWL
	 *            The value to set
	 */
	public void setInWL(final boolean inWL) {
		this.mInWL = inWL;
	}

	/**
	 * Sets the progress measure of this vertex as needed for the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ASimulation
	 * ASimulation}.
	 * 
	 * @param pm
	 *            The progress measure to set
	 */
	public void setPM(final int pm) {
		this.mPm = pm;
	}

	/**
	 * Sets the priority of the vertex.
	 * 
	 * @param priority
	 *            The priority to set
	 */
	public void setPriority(final int priority) {
		this.mPriority = priority;
	}
}
