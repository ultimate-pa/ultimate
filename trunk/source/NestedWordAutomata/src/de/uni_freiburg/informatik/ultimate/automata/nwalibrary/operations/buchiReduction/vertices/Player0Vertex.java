/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices;

/**
 * @author Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * @author Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * @date 16.01.2012
 */
public class Player0Vertex<LETTER,STATE> extends Vertex<LETTER, STATE> {
    /**
     * The label of the edge in the buchi automaton.
     */
    private LETTER a;

    /**
     * Vertex constructor.
     * 
     * @param priority
     *            priority of this vertex
     * @param b
     *            extra bit b
     * @param q0
     *            label of the first Buchi automaton state
     * @param q1
     *            label of the second Buchi automaton state
     * @param a
     *            label of the Buchi automaton edge
     */
    public Player0Vertex(byte priority, boolean b, STATE q0, STATE q1, LETTER a) {
        super(priority, b, q0, q1);
        this.a = a;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("<").append(isB()).append(",(").append(getQ0()).append(",");
        sb.append(getQ1()).append(",").append(a).append("),p:");
        sb.append(getPriority()).append(",pm:").append(pm);
        sb.append(">");
        return sb.toString();
    }
}