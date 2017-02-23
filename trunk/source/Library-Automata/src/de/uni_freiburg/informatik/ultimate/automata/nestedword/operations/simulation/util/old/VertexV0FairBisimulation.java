/*
 * Copyright (C) 2011-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
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
/**
 * Vertex for fair bi-simulation.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.old;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @date 16.12.2011
 */
public class VertexV0FairBisimulation<LETTER, STATE> extends VertexV0Delayed<LETTER, STATE> {
	/*_______________________________________________________________________*\
	\* FIELDS / ATTRIBUTES                                                   */

	/**
	 * The extra bit b2.
	 */
	private boolean b2;

	/*_______________________________________________________________________*\
	\* CONSTRUCTORS                                                          */

	/**
	 * Vertex constructor.
	 * 
	 * @param priority
	 *            the priority of this vertex
	 * @param b1
	 *            the extra bit b1
	 * @param b2
	 *            the extra bit b2
	 * @param q0
	 *            the label of the first Buchi automaton state
	 * @param q1
	 *            the label of the second Buchi automaton state
	 * @param a
	 *            the label of the Buchi automaton edge
	 */
	public VertexV0FairBisimulation(int priority, boolean b1, boolean b2, STATE q0, STATE q1, LETTER a) {
		super(priority, b1, q0, q1, a);
		this.setB2(b2);
	}

	/**
	 * Vertex constructor.
	 * 
	 * @param copy
	 *            the Vertex to copy
	 */
	public VertexV0FairBisimulation(VertexV0FairBisimulation<LETTER, STATE> copy) {
		this(copy.getPriority(), copy.isB1(), copy.isB2(), copy.getQ0(), copy.getQ1(), copy.getA());
	}

	/*_______________________________________________________________________*\
	\* METHODS                                                               */

	/*_______________________________________________________________________*\
	\* OVERRIDDEN METHODS                                                    */

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("<").append(isB1()).append(",").append(isB2()).append(",(");
		sb.append(getQ0()).append(",").append(getQ1()).append("),p:");
		sb.append(getPriority()).append(",pm:").append(getPM());
		sb.append(">");
		return sb.toString();
	}

	/*_______________________________________________________________________*\
	\* GETTERS AND SETTERS                                                   */

	/**
	 * Getter for the extra bit b1.
	 * 
	 * @return the b1
	 */
	public boolean isB1() {
		// just to make the interface intuitive!
		return super.isB();
	}

	/**
	 * Getter for the extra bit b2.
	 * 
	 * @return the b2
	 */
	public boolean isB2() {
		return b2;
	}

	/**
	 * Setter for the extra bit b2.
	 * 
	 * @param b2
	 *            the b2 to set
	 */
	public void setB2(boolean b2) {
		this.b2 = b2;
	}

	/**
	 * Returns q0 if stateNumber == false, q1 otherwise
	 * 
	 * @param stateNumber
	 *            number of state to return.
	 * @return state
	 */
	public STATE getQ(boolean stateNumber) {
		if (stateNumber) {
			return getQ1();
		} else {
			return getQ0();
		}
	}
}
