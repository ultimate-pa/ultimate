/* $Id: PEA2ARMCConverter.java 328 2008-08-06 11:19:16Z jfaber $ 
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
package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.armc;

import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.PEA2TCSConverter;

/**
 * PEA2ARMCConverter is the new converter from Phase Event Automata into
 * Transition Constraint Systems in ARMC syntax.
 * It replaces the now deprecated {@link de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.PEA2ARMCConverter}
 * and is slightly more efficient and much more expandable and maintainable.
 *
 * @author jfaber
 *
 */
public class PEA2ARMCConverter {



        /**
         * Converts a PEA into a Transition Constraint System and writes it
         * in ARMC syntax to an output file.
         * (Location names are preserved.)
         * 
         * @param pea
         *      input PEA
         * @param file
         *      file name for the ARMC output
         */
        public static void convert(PhaseEventAutomata pea, String file)
        {
            convert(pea, file, false);
        }
    
        /**
         * Converts a PEA into a Transition Constraint System and writes it
         * in ARMC syntax to an output file.
         * 
         * @param pea
         *      input PEA
         * @param file
         *      file name for the ARMC output
         * @param rename
         *      If <code>true</code> locations in the PEA are renamed into a
         *      default name (sometimes easier to handle).
         *      If <code>true</code> location names are preserved.
         */
	public static void convert(PhaseEventAutomata pea, 
			    String file, 
			    boolean rename) {
	    final PEA2TCSConverter armcConverter = 
	        new PEA2TCSConverter(new ARMCWriter(file, rename),
                                     pea);
	    armcConverter.useBooleanDecision();
	    armcConverter.convert();
	}



}
