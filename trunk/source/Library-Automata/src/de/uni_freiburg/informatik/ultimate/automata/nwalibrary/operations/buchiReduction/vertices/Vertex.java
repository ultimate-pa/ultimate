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

import java.util.Set;

public class Vertex<LETTER,STATE> {
    /**
     * The label of the first Buchi automaton state.
     */
    private STATE q0;
    /**
     * The label of the second Buchi automaton state.
     */
    private STATE q1;
    /**
     * The extra bit b.
     */
    private boolean b;
    /**
     * The priority of this vertex.
     */
    private byte priority;
    /**
     * The progressMeasure for Jurdzinski lifting function.
     */
    protected int pm;
    /**
     * The b required for the efficient lifting algorithm implementation.
     */
    private int bEff;
    /**
     * The c required for the efficient lifting algorithm implementation.
     */
    private int c;
    /**
     * Whether this vertex is in the working list or not.
     */
    private boolean inWL;

    /**
     * Constructor.
     * 
     * @param priority
     *            priority of this vertex
     * @param b
     *            extra bit b
     * @param q0
     *            label of the first Buchi automaton state
     * @param q1
     *            label of the second Buchi automaton state
     */
    public Vertex(byte priority, boolean b, STATE q0, STATE q1) {
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

    /**
     * Getter for the extra bit b.
     * 
     * @return the b
     */
    public boolean isB() {
        return b;
    }

    /**
     * Getter for the priority of this vertex.
     * 
     * @return the priority
     */
    public byte getPriority() {
        return priority;
    }

    /**
     * 
     * @return the progress measure
     */
	// if we compute progress measures for each SCC separately
	// and this is not in the current SCC we interpret the PM
	// of w as 0 it the PM is < infinity
    /**
     * FIXME @Matthias document this!
     * @param scc
     * @param infinity
     * @return
     */
    public int getPM(Set<Vertex<LETTER,STATE>> scc, int infinity) {
    	if (scc == null) {
    		return pm;
    	}
    	else if (pm == infinity) {
    		return infinity;
    	}
    	else if (scc.contains(this)) {
    		return pm;
    	}
    	else {
    		return 0;
    	}
    }

    /**
     * Setter for ProgressMeasure.
     * 
     * @param pm
     *            the progress measure
     */
    public void setPM(int pm) {
        this.pm = pm;
    }

    /**
     * Getter for b.
     * 
     * @return the b
     */
    public int getBEff() {
        return bEff;
    }

    /**
     * Setter for b.
     * 
     * @param b
     *            the b to set
     */
    public void setBEff(int b) {
        this.bEff = b;
    }

    /**
     * Getter for c.
     * 
     * @return the c
     */
    public int getC() {
        return c;
    }

    /**
     * Setter for c.
     * 
     * @param c
     *            the c to set
     */
    public void setC(int c) {
        this.c = c;
    }

    /**
     * Returns false if in v0 and true if in v1.
     * 
     * @return false if in v0 and true if in v1
     */
    public boolean isInV1() {
        return !(this instanceof Player0Vertex);
    }
    
    /**
     * Returns true if in v0 and false if in v1.
     * 
     * @return true if in v0 and false if in v1
     */
    public boolean isInV0() {
        return this instanceof Player0Vertex;
    }

    /**
     * Whether this vertex is in the working list.
     * 
     * @return true if in working list
     */
    public boolean isInWL() {
        return inWL;
    }

    /**
     * Set flag, if in working list.
     * 
     * @param inWL the inWL to set
     */
    public void setInWL(boolean inWL) {
        this.inWL = inWL;
    }
}
