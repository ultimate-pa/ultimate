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
package de.uni_freiburg.informatik.ultimate.lib.pea;

import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.DCPhase;

/**
 * @author roland
 */
public class PhaseBits implements Comparable {

    /* set of active phases */
    int active;

    /* for GREATER or LESS phases, is the bound exact, i.e. >= or <= */
    int exactbound;

    /* set of waiting phases (i.e. lower timebound) */
    int waiting;

    public PhaseBits(int active, int exactbound, int waiting) {
        this.active = active;
        this.exactbound = exactbound;
        this.waiting = waiting;
    }

    @Override
	public int hashCode() {
        return active ^ (exactbound << 10 | exactbound >> 22)
                ^ (waiting << 20 | waiting >> 12);
    }

    @Override
	public boolean equals(Object o) {
        return (o instanceof PhaseBits && active == ((PhaseBits) o).active
                && exactbound == ((PhaseBits) o).exactbound && waiting == ((PhaseBits) o).waiting);
    }

    @Override
	public String toString() {
        final StringBuffer sb = new StringBuffer("st");
        String delim = "";
        for (int i = 0, bit = 1; bit <= active; i++, bit += bit) {
            if ((active & bit) == 0) {
				continue;
			}
            sb.append(delim).append(i);
            if ((exactbound & bit) != 0) {
				sb.append('X');
			} else if ((waiting & bit) != 0) {
				sb.append('W');
			}
            delim = "";
        }
        return sb.toString();
    }

    @Override
	public int compareTo(Object other) {
        final PhaseBits o = (PhaseBits) other;
        if (active != o.active) {
			return active - o.active;
		}
        if (waiting != o.waiting) {
			return o.waiting - waiting;
		}
        return exactbound - o.exactbound;
    }
    
    public int getActive() {
    	return active;
    }

    public int getWaiting() {
    	return waiting;
    }

    public int getExactBound() {
    	return exactbound;
    }

    /** transform this PhaseBits object into a PhaseSet for easier access */
    public PhaseSet getPhaseSet(DCPhase phases[]) {
        final PhaseSet ps = new PhaseSet();
        for (int i = 0, bit = 1; bit <= active; i++, bit += bit) {
            if ((active & bit) == 0) {
				continue;
			}
            final DCPhase ph = phases[i];
            final boolean exact = (exactbound & bit) != 0;
            if ((waiting & bit) != 0) {
				ps.addWaitingPhase(ph, exact);
			} else {
				ps.addPhase(ph, exact);
			}
        }
        return ps;
    }
}
