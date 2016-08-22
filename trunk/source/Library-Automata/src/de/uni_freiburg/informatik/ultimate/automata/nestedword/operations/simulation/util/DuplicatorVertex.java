/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util;

/**
 * A vertex representing that its <i>Duplicator</i>s turn in the game defined by
 * a
 * {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.AGameGraph
 * AGameGraph}.<br/>
 * <br/>
 * 
 * The vertex representation is <b>(q0, q1, a, bit)</b> which means
 * <i>Spoiler</i> is currently at state q0 and made a move using an a-transition
 * before whereas <i>Duplicator</i> now is at q1 and must try to also use an
 * a-transition. The bit encodes extra information if needed.
 * 
 * @author Daniel Tischner
 * @author Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * @author Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * @date 16.01.2012
 * 
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public class DuplicatorVertex<LETTER, STATE> extends Vertex<LETTER, STATE> {
	/**
	 * The label of the corresponding transition in the buchi automaton.
	 */
	private final LETTER a;

	/**
	 * Constructs a new duplicator vertex with given representation <b>(q0, q1,
	 * a, bit)</b> which means <i>Spoiler</i> is currently at state q0 and made
	 * a move using an a-transition before whereas <i>Duplicator</i> now is at
	 * q1 and must try to also use an a-transition. The bit encodes extra
	 * information if needed.
	 * 
	 * @param priority
	 *            The priority of the vertex
	 * @param b
	 *            The extra bit of the vertex
	 * @param q0
	 *            The state spoiler is at
	 * @param q1
	 *            The state duplicator is at
	 * @param a
	 *            The letter spoiler used before
	 */
	public DuplicatorVertex(final int priority, final boolean b, final STATE q0, final STATE q1, final LETTER a) {
		super(priority, b, q0, q1);
		this.a = a;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (!super.equals(obj)) {
			return false;
		}
		if (!(obj instanceof DuplicatorVertex)) {
			return false;
		}
		@SuppressWarnings("rawtypes")
		final DuplicatorVertex other = (DuplicatorVertex) obj;
		if (a == null) {
			if (other.a != null) {
				return false;
			}
		} else if (!a.equals(other.a)) {
			return false;
		}
		return true;
	}

	/**
	 * Gets the letter.
	 * 
	 * @return the letter
	 */
	public LETTER getLetter() {
		return a;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.vertices.Vertex#getName()
	 */
	@Override
	public String getName() {
		return isB() + "," + getQ0() + "," + getQ1() + "," + getLetter();
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
		result = prime * result + ((a == null) ? 0 : a.hashCode());
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
		sb.append(getQ1()).append(",").append(a).append("),p:");
		sb.append(getPriority()).append(",pm:").append(mPm);
		sb.append(">");
		return sb.toString();
	}
}
