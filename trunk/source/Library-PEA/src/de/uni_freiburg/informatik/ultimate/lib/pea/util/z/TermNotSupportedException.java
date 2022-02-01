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

package de.uni_freiburg.informatik.ultimate.lib.pea.util.z;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.SectionInfo;

/**
 * TermNotSupportedExpression is a RuntimeException to be used when a Z term
 * that can be handeled by Syspect in principle (input, latex export, XML export)
 * but is not supported for a particular export or conversion.
 *
 * @author jfaber
 *
 */
public class TermNotSupportedException extends RuntimeException {

    
    public static final String Z_TERmNOT_SUPPORTED_IN_CURRENT_OPERATION = "Z term not supported in current operation: ";
    
    private static final long serialVersionUID = -395464031262474943L;
    
    /**
     * Contains the term that cannot be handled in a particular export. 
     */
    ZTerm unsupportedTerm;
    
    /**
     * @param arg0
     *          The unsupported ZTerm object.
     */
    public TermNotSupportedException(ZTerm arg0) {
        unsupportedTerm = arg0;
    }

    /**
     * @param arg0
     *          The unsupported Term object.
     * @param sectInfo
     *          The SectionInfo necessary to translate the term back into a unicode
     *          representation.
     * 
     */
    public TermNotSupportedException(Term arg0, SectionInfo sectInfo) {
        unsupportedTerm = new ZTerm(arg0, sectInfo);
    }

    /**
     * @return Returns the unsupportedTerm.
     */
    public ZTerm getUnsupportedTerm() {
        return unsupportedTerm;
    }

    /**
     * @return Returns the unsupportedTerm as unicode representation.
     */
    public String getUnsupportedTermAsUnicode() {
        return ZWrapper.INSTANCE.termToUnicode(unsupportedTerm);
    }

    
    /* (non-Javadoc)
     * @see java.lang.Throwable#toString()
     */
    @Override
    public String toString() {
        return Z_TERmNOT_SUPPORTED_IN_CURRENT_OPERATION + 
            getUnsupportedTermAsUnicode();
    }
    
    

}
