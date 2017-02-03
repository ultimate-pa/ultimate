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

package de.uni_freiburg.informatik.ultimate.lib.pea.test;

import java.util.ArrayList;
import java.util.LinkedList;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.PEANet;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.ZDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.PEAJ2XMLConverter;

/**
 * OurPea is a test class for the pea tool.
 * 
 * @author jdq
 * 
 */
public final class OurPea {

    private OurPea() {
        super();
    }

    @SuppressWarnings("deprecation")
    public static void main(final String[] args) {
        PhaseEventAutomata pea;
        final Phase[] phases = new Phase[2];

        try {
            phases[0] = new Phase("{0}", ZDecision.createSimplified("\u2577 x: \u2119 [] | x \u2029")); //TODO what is this for?
        } catch (final Exception e) {
            e.printStackTrace();
        }
        phases[1] = new Phase("{0,1}");
        // phases[0] = new Phase("{0}");
        final String[] resets = { "c" };
        phases[0].addTransition(phases[1], CDD.TRUE, resets);
        phases[1].addTransition(phases[0], CDD.TRUE, new String[0]);
        phases[0].addTransition(phases[0], CDD.TRUE, new String[0]);
        phases[1].addTransition(phases[1], CDD.TRUE, new String[0]);
        final LinkedList<String> l = new LinkedList<>();
        l.add(resets[0]);
        pea = new PhaseEventAutomata("ourPEA", phases, phases.clone(), l);
        pea.dump();
        try {
            final PEAJ2XMLConverter conv = new PEAJ2XMLConverter();

            final ArrayList<PhaseEventAutomata> peaList = new ArrayList<>();
            peaList.add(pea);
            final PEANet peanet = new PEANet();
            peanet.setPeas(peaList);
            conv.convert(peanet, "/tmp/test.xml");
        } catch (final Exception e) {
            e.printStackTrace();
        }
    }
}
