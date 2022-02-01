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
 * Vertex for fair, direct and ordinary simulation.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.old;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @date 10.12.2011
 */
public class VertexV0<LETTER, STATE> extends VertexV1<LETTER, STATE> {
	/*_______________________________________________________________________*\
	\* FIELDS / ATTRIBUTES                                                   */

	/**
	 * The label of the edge in the Buchi automaton.
	 */
	private final LETTER a;

	/*_______________________________________________________________________*\
	\* CONSTRUCTORS                                                          */

	/**
	 * Constructor.
	 * 
	 * @param priority
	 *            the priority of this vertex
	 * @param q0
	 *            the label of the first Buchi automaton state
	 * @param q1
	 *            the label of the second Buchi automaton state
	 * @param a
	 *            the label of the Buchi automaton edge
	 */
	public VertexV0(int priority, STATE q0, STATE q1, LETTER a) {
		super(priority, q0, q1);
		this.a = a;
	}

	/*_______________________________________________________________________*\
	\* METHODS                                                               */

	/*_______________________________________________________________________*\
	\* OVERRIDDEN METHODS                                                    */

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("<(").append(getQ0()).append(",").append(getQ1());
		sb.append(",").append(getA()).append("),p:").append(getPriority());
		sb.append(",pm:").append(getPM()).append(">");
		return sb.toString();
	}

	/*_______________________________________________________________________*\
	\* GETTERS AND SETTERS                                                   */

	/**
	 * Getter for the label of the Buchi automaton edge.
	 * 
	 * @return the label
	 */
	public LETTER getA() {
		return a;
	}
}
