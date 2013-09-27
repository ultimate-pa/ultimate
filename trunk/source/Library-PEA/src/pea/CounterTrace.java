/*
 *
 * This file is part of the PEA tool set
 * 
 * The PEA tool set is a collection of tools for 
 * Phase Event Automata (PEA). See
 * http://csd.informatik.uni-oldenburg.de/projects/peatools.html
 * for more information.
 * 
 * Copyright (C) 2005-2006, Department for Computing Science,
 *                          University of Oldenburg
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA
 */
package pea;

import java.util.*;

import net.sourceforge.czt.z.util.ZString;

/**
 * Represents a counter example trace.  A counter example trace is a
 * sequence of phases (represented by CounterTrace.DCPhase).  Each phase
 * has an invariant, a set of forbidden events, a set of entry events and
 * an optional upper or lower bound.
 */
public class CounterTrace {
    public static final int BOUND_LESS         = -2;
    public static final int BOUND_LESSEQUAL    = -1;
    public static final int BOUND_NONE         =  0;
    public static final int BOUND_GREATEREQUAL =  1;
    public static final int BOUND_GREATER      =  2;

    public static class DCPhase {
	/**
         * @return Returns the allowEmpty.
         */
        public boolean isAllowEmpty() {
            return allowEmpty;
        }

    CDD        entryEvents;
	CDD        invariant;
	int        boundType;
	int        bound;
	Set        forbid;
	boolean    allowEmpty;
	
	public DCPhase(CDD ee, CDD i, int bt, int b, Set f, boolean empty) {
	    entryEvents = ee;
	    invariant   = i;
	    bound       = b;
	    /* the current implementation of Trace2PEACompiler requires (for non-empty
	     * phases) that
	     * \ell > 0 and \ell \geq 0 are modelled with boundType = BOUND_NONE
	     */
	    boundType   = (!allowEmpty && b == 0 && bt > 0 ? BOUND_NONE : bt);
	    forbid      = f;
	    allowEmpty  = empty;
	}

//	public DCPhase(CDD i, int bt, int b, Set f, boolean empty) {
//	    this(CDD.TRUE, i, bt, b, f, empty);
//	}

	public DCPhase(CDD ee, CDD i, int bt, int b, Set f) {
	    this(ee, i, bt, b, f, false);
	}

	public DCPhase(CDD i, int bt, int b, Set f) {
	    this(CDD.TRUE, i, bt, b, f, false);
	}

	public DCPhase(CDD ee, CDD i, Set f) {
	    this(ee, i, BOUND_NONE, 0, f, false);
	}

	public DCPhase(CDD i, Set f) {
	    this(CDD.TRUE, i, BOUND_NONE, 0, f, false);
	}

	public DCPhase(CDD ee, CDD i, int bt, int b) {
	    this(ee, i, bt, b, Collections.EMPTY_SET, false);
	}

	public DCPhase(CDD i, int bt, int b) {
	    this(CDD.TRUE, i, bt, b, Collections.EMPTY_SET, false);
	}

	public DCPhase(CDD ee, CDD i) {
	    this(ee, i, BOUND_NONE, 0, Collections.EMPTY_SET, false);
	}

	public DCPhase(CDD i) {
	    this(CDD.TRUE, i, BOUND_NONE, 0, Collections.EMPTY_SET, false);
	}

	/**
	 * Create a ell ~ bound phase (with allowEmpty set if no lower bound).
	 */
	public DCPhase(int bt, int b) {
	    this(CDD.TRUE, CDD.TRUE, bt, b, Collections.EMPTY_SET, bt <= 0);
	}

	/**
	 * Create a true phase (with allowEmpty set).
	 */
	public DCPhase() {
	    this(CDD.TRUE, CDD.TRUE, BOUND_NONE, 0, 
		 Collections.EMPTY_SET, true);
	}
	
	/**
	 * @param bound The bound to set.
	 */
	public void setBound(int bound) {
		this.bound = bound;
	}
	/**
	 * @param boundType The boundType to set.
	 */
	public void setBoundType(int boundType) {
		this.boundType = boundType;
	}
	/**
	 * @param forbid The forbid to set.
	 */
	public void setForbid(Set forbid) {
		this.forbid = forbid;
	}
	/**
	 * @param predicate The predicate to set.
	 */
	public void setInvariant(CDD predicate) {
		this.invariant = predicate;
	}

        public String toString(boolean useUnicode) {
            String AND = useUnicode ? ZString.AND : "/\\";
            String NOEVENT = useUnicode ? "\u229F" : "[-]";
            String GEQ = useUnicode ? ZString.GEQ : ">=";
            String LEQ = useUnicode ? ZString.LEQ : "<=";
            String LCEIL = useUnicode ? "\u23A1" : "[";
            String RCEIL = useUnicode ? "\u23A4" : "]";
            String ELL = useUnicode ? "\u2113" : "L";

            StringBuilder sb = new StringBuilder();
            if (entryEvents != CDD.TRUE)
                sb.append(entryEvents).append(" ; ");

            if(invariant == CDD.TRUE && allowEmpty){
                sb.append(invariant);
            }else{
                sb.append(LCEIL).append(invariant).append(RCEIL);
            }
            
            for (Iterator it = forbid.iterator(); it.hasNext(); )
                sb.append(' ').append(AND).append(' ').append(NOEVENT)
                    .append(' ').append(it.next());

            if (boundType != BOUND_NONE) {
                sb.append(' ').append(AND).append(' ').append(ELL);
                switch (boundType) {
                case BOUND_LESS:
                    sb.append(" < ");
                    break;
                case BOUND_LESSEQUAL:
                    sb.append(' ').append(LEQ).append(' ');
                    break;
                case BOUND_GREATER:
                    sb.append(" > ");
                    break;
                case BOUND_GREATEREQUAL:
                    sb.append(' ').append(GEQ).append(' ');
                    break;
                }
                sb.append(bound);
            }

            return sb.toString();
        }

        @Override
        public String toString()
        {
            return toString(true);
        }
        
        /**
         * Prints a dump of this DCPhase to stderr. 
         */
        public void dump() {
            System.err.print(toString(true));
        }

        /**
         * @return Returns the boundType.
         */
        public int getBoundType() {
            return boundType;
        }

        /**
         * @return Returns the forbid.
         */
        public Set getForbid() {
            return forbid;
        }

        /**
         * @return Returns the invariant.
         */
        public CDD getInvariant() {
            return invariant;
        }
        
    }

    DCPhase[] phases;

    public CounterTrace(DCPhase[] phases) {
	this.phases = phases;
    }

    public DCPhase[] getPhases()
    {
        return phases;
    }

    /**
     * Prints a dump of this DCPhase to stderr. 
     */
    public void dump() {
        System.err.print(phases.length + ":  ! ( ");
        for (int i = 0; i < phases.length; i++) {
            phases[i].dump();
            if(i<phases.length-1)
                System.err.print(" ; ");
        }
        System.err.println(" )");
    }
}
