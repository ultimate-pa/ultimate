/* $Id: PEANet.java 342 2008-08-15 10:12:25Z jfaber $ 
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


/**
 * PEANet is a network of PEA including the needed type declarations.
 * 
 * @author cthulhu
 * 
 */
public class PEANet {

    /**
     * A list of global type and constant declarations. The exact syntax can be freely defined and usually
     * depends on the context in which this PEANet is used.
     */
    private ArrayList<String> declarations;

    private ArrayList<PhaseEventAutomata> peas;

    /**
     * Constructor for creating a new network without PEA and declarations
     * 
     */
    public PEANet() {
        declarations = new ArrayList<String>();
        peas = new ArrayList<PhaseEventAutomata>();
    }

    /**
     * Constructor for creating a new network out of the given PEA and
     * declarations
     * 
     * @param declarations
     *            the Z type declarations
     * @param peas
     *            the list of PEA which form the network
     */
    public PEANet(ArrayList<String> declarations,
            ArrayList<PhaseEventAutomata> peas) {
        this.declarations = declarations;
        this.peas = peas;
    }

    /**
     * adds the given PEA to this network
     * 
     * @param pea
     *            the PEA to add to the network
     * @returns false, if the PEA was already contained in the network, true
     *          else.
     */
    public boolean addPEA(PhaseEventAutomata pea) {
        if (peas.contains(pea)) {
            return false;
        }
        peas.add(pea);
        return true;
    }

    /**
     * adds the given Z type declaration to the network
     * 
     * @param decl
     *            the declaration to add to the network
     * @return false, if the declaration was already contained in the network,
     *         true else.
     */
    public boolean addDeclaration(String decl) {
        if (declarations.contains(decl)) {
            return false;
        }
        declarations.add(decl);
        return true;
    }

    /**
     * @return Returns the Z type declarations of this network
     */
    public ArrayList<String> getDeclarations() {
        return declarations;
    }

    /**
     * @param declarations
     *            The Z type declarations to set.
     */
    public void setDeclarations(ArrayList<String> declarations) {
        this.declarations = declarations;
    }

    /**
     * @return Returns the list of PEA of the network.
     */
    public ArrayList<PhaseEventAutomata> getPeas() {
        return peas;
    }

    /**
     * @param peas
     *            The list of PEA to set.
     */
    public void setPeas(ArrayList<PhaseEventAutomata> peas) {
        this.peas = peas;
    }

}
