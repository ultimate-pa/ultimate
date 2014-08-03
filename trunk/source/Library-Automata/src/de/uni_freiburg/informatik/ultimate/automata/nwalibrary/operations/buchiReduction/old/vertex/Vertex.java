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
/**
 * Basic Vertex.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.old.vertex;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @date 10.12.2011
 */
public class Vertex<LETTER,STATE> {
    /*_______________________________________________________________________*\
    \* FIELDS / ATTRIBUTES                                                   */
	
    /**
     * The label of the first Buchi automaton state.
     */
    private STATE q0;
    /**
     * The label of the second Buchi automaton state.
     */
    private STATE q1;
	
    /*_______________________________________________________________________*\
    \* CONSTRUCTORS                                                          */
    
    /**
     * Constructor.
	 * 
     * @param q0
     *            the label of the first Buchi automaton state
     * @param q1
     *            the label of the second Buchi automaton state
     */
    public Vertex(STATE q0, STATE q1) {
        this.q0 = q0;
        this.q1 = q1;
    }
    
    /*_______________________________________________________________________*\
    \* METHODS                                                               */
    
    /*_______________________________________________________________________*\
    \* OVERRIDDEN METHODS                                                    */
    
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("<(").append(getQ0()).append(",").append(getQ1());
        sb.append(")>");
        return sb.toString();
    }
    
    /*_______________________________________________________________________*\
    \* GETTERS AND SETTERS                                                     */
    
    /**
     * Getter for the label of the first Buchi automaton state.
     * 
     * @return the label of the first Buchi automaton state
     */
    public STATE getQ0() {
        return q0;
    }

    /**
     * Getter for the label of the first Buchi automaton state.
     * 
     * @return the label of the first Buchi automaton state
     */
    public STATE getQ1() {
        return q1;
    }
}
