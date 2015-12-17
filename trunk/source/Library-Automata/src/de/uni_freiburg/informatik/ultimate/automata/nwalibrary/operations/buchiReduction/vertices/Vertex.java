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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices;

import java.util.Set;

/**
 * A vertex base class for the game defined by a
 * {@link de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.AGameGraph
 * AGameGraph}.<br/>
 * <br/>
 * 
 * The vertex representation is <b>(q0, q1, bit)</b> which means <i>Spoiler</i>
 * is currently at state q0 whereas <i>Duplicator</i> now is at q1. The bit
 * encodes extra information if needed.<br/>
 * A vertex also holds several fields used for simulation calculation, for more
 * information see
 * {@link de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.ASimulation
 * ASimulation}.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public class Vertex<LETTER, STATE> {
	/**
	 * The bit encodes extra information if needed.
	 */
	private boolean b;
	/**
	 * The best neighbor measure of this vertex as needed for the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.ASimulation
	 * ASimulation}.
	 */
	private int bEff;
	/**
	 * The neighbor counter of this vertex as needed for the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.ASimulation
	 * ASimulation}.
	 */
	private int c;
	/**
	 * Whether this vertex is in the working list of the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.ASimulation
	 * ASimulation} or not.
	 */
	private boolean inWL;
	/**
	 * The priority of this vertex as needed for the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.ASimulation
	 * ASimulation}.
	 */
	private int priority;
	/**
	 * The label of the first buechi automaton state where <i>Spoiler</i>
	 * currently is at.
	 */
	private STATE q0;
	/**
	 * The label of the second buechi automaton state where <i>Duplicator</i>
	 * currently is at.
	 */
	private STATE q1;
	/**
	 * The progress measure of this vertex as needed for the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.ASimulation
	 * ASimulation}.
	 */
	protected int pm;

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
	public Vertex(int priority, boolean b, STATE q0, STATE q1) {
		this.q0 = q0;
		this.q1 = q1;
		this.b = b;
		this.priority = priority;
		this.pm = 0;
		this.bEff = 0;
		this.c = 0;
		this.setInWL(false);
	}

	/**
	 * Gets the best neighbor measure of this vertex as needed for the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.ASimulation
	 * ASimulation}.
	 * 
	 * @return The best neighbor measure of this vertex
	 */
	public int getBEff() {
		return bEff;
	}

	/**
	 * Gets the neighbor counter of this vertex as needed for the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.ASimulation
	 * ASimulation}.
	 * 
	 * @return The neighbor counter of this vertex
	 */
	public int getC() {
		return c;
	}

	/**
	 * Gets the progress measure of this vertex as needed for the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.ASimulation
	 * ASimulation}.
	 * 
	 * @param scc
	 *            The SCC currently working from
	 * @param infinity
	 *            The currently known upper bound for infinity, for more
	 *            information see
	 *            {@link de.uni_freiburg.informatik.ultimate.automata.nwalibrary. operations.buchiReduction.AGameGraph#getGlobalInfinity()
	 *            AGameGraph.getGlobalInfinity()}.
	 * @return The progress measure of this vertex or 0 if the SCC is not
	 *         <tt>null</tt> and not contains this vertex
	 */
	public int getPM(Set<Vertex<LETTER, STATE>> scc, int infinity) {
		if (scc == null) {
			return pm;
		} else if (pm == infinity) {
			return infinity;
		} else if (scc.contains(this)) {
			return pm;
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
		return priority;
	}

	/**
	 * Gets the label of the first buechi automaton state where <i>Spoiler</i>
	 * currently is at.
	 * 
	 * @return The label of the first buechi automaton state where
	 *         <i>Spoiler</i> currently is at.
	 */
	public STATE getQ0() {
		return q0;
	}

	/**
	 * Gets the label of the second buechi automaton state where
	 * <i>Duplicator</i> currently is at.
	 * 
	 * @return The label of the second buechi automaton state where
	 *         <i>Duplicator</i> currently is at.
	 */
	public STATE getQ1() {
		return q1;
	}

	/**
	 * Returns the bit which encodes extra information if needed.
	 * 
	 * @return True if the bit which encodes extra information if needed is
	 *         true, false if not.
	 */
	public boolean isB() {
		return b;
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
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.ASimulation
	 * ASimulation} or not.
	 * 
	 * @return True if this vertex is in the working list, false if not.
	 */
	public boolean isInWL() {
		return inWL;
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
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.ASimulation
	 * ASimulation}.
	 * 
	 * @param b
	 *            The best neighbor measure to set
	 */
	public void setBEff(int b) {
		this.bEff = b;
	}

	/**
	 * Sets the neighbor counter of this vertex as needed for the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.ASimulation
	 * ASimulation}.
	 * 
	 * @param c
	 *            The neighbor counter to set
	 */
	public void setC(int c) {
		this.c = c;
	}

	/**
	 * Sets whether this vertex is in the working list of the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.ASimulation
	 * ASimulation} or not.
	 * 
	 * @param inWL
	 *            The value to set
	 */
	public void setInWL(boolean inWL) {
		this.inWL = inWL;
	}

	/**
	 * Sets the progress measure of this vertex as needed for the
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.ASimulation
	 * ASimulation}.
	 * 
	 * @param pm
	 *            The progress measure to set
	 */
	public void setPM(int pm) {
		this.pm = pm;
	}

	/**
	 * Sets the priority of the vertex.
	 * 
	 * @param priority
	 *            The priority to set
	 */
	public void setPriority(final int priority) {
		this.priority = priority;
	}
}
