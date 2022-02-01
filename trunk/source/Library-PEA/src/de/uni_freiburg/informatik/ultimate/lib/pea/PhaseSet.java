/* $Id$
 *
 * This file is part of the PEA tool set
 * 
 * The PEA tool set is a collection of tools for Phase Event Automata
 * (PEA).
 * 
 * Copyright (C) 2005-2006, Carl von Ossietzky University of Oldenburg
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

import java.util.ArrayList;
import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.DCPhase;

/**
 * PhaseSet is a set of DCPhases, some of which might have the
 * 'waiting' or 'exact' bit
 *
 * @author ulli
 *
 */
public class PhaseSet {
    private final ArrayList<DCPhase> phases, waiting, exact;

    public PhaseSet() {
        phases = new ArrayList<>();
        waiting = new ArrayList<>();
        exact = new ArrayList<>();
    }

    public void addPhase(final DCPhase ph, final boolean isExact) {
        phases.add(ph);
        if (isExact) {
			exact.add(ph);
		}
    }
    
    public ArrayList<DCPhase> getPhases(){
    	return this.phases;
    }

    public void addWaitingPhase(final DCPhase ph, final boolean isExact) {
        addPhase(ph, isExact);
        waiting.add(ph);
    }

    public int getNumberOfPhases()
    {
        return phases.size();
    }

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        if (phases.isEmpty()) {
			return "";
		}
        final Iterator<DCPhase> it = phases.iterator();
        sb.append("    ").append(it.next());
        while (it.hasNext()) {
            final DCPhase ph = it.next();
            sb.append("\n    ").append(ph);
            if (waiting.contains(ph)) {
				sb.append(" (waiting)");
			}
        }
        return sb.toString();
    }
}
