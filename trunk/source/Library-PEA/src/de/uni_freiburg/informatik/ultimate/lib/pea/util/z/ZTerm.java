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
import net.sourceforge.czt.session.SectionManager;


/**
 * ZTerm is a simple container for a Z term with its associated SectionInfo object, which is
 * necessary to retranslate a Z term into unicode representation.
 *
 * @author jfaber
 *
 */
public class ZTerm {
   
    Term term;
    SectionInfo sectionInfo;

    public ZTerm(Term term, SectionInfo info) {
        this.term = term;
        sectionInfo = info;
    }

    public SectionInfo cloneSectionInfo() {
        return ((SectionManager) sectionInfo).clone();
    }
    
    public SectionInfo resetSectionInfo() {
        ((SectionManager) sectionInfo).reset();
        return sectionInfo ;
    }

    /**
     * @return Returns the sectionInfo.
     */
    public final SectionInfo getSectionInfo() {
        return sectionInfo;
    }
    
    
    /**
     * @return Returns the term.
     */
    public Term getTerm() {
        return term;
    }

}
