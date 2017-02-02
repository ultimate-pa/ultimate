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

import java.io.StringWriter;

import net.sourceforge.czt.oz.jaxb.JaxbXmlWriter;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.print.oz.PrintUtils;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;

/**
 * ZWrapper is a (abstract) wrapper to write Z predicates and declarations to ZML.
 * Syspect uses the implementation de.syspect.export.pea.converter.ZWrapperImpl.
 *
 * @author jfaber
 *
 */
public class ZWrapper {
    
    protected final String DEFAULT_SECTIONNAME = null;
    
    public static ZWrapper INSTANCE=new ZWrapper();

    protected ZWrapper(){
    }
    
    protected void instantiate() {
        if(this.getClass() != ZWrapper.class) {
			INSTANCE = this;
		}
    }
    
    /**
     * Takes a Z predicate as String and return a String containing the ZML representation of the string.
     * @param predicate
     * @return
     */
    public String predicateToZml(final String predicate) throws ParseException,
        InstantiationException {
        throw new InstantiationException("ZWrapper cannot be used directly. Use a derived class.");
    }
    
    /**
     * Takes a Z predicate as String and returns
     * term representation of the string.
     * @param predicate
     * @return
     */
    public ZTerm predicateToTerm(final String predicate) throws ParseException,
        InstantiationException {
        throw new InstantiationException("ZWrapper cannot be used directly. Use a derived class.");
    }
    
    /**
     * Takes a Z declaration as unicode string and returns a ZML expression for this Declaration.
     * @param term
     * @return
     */
    public String declToZml(final String term)  throws ParseException,
    InstantiationException {
        throw new InstantiationException("ZWrapper cannot be used directly. Use a derived class.");
    }
    
    /**
     * Takes a ZDeclaration and returns a ZML expression for this Declaration.
     * @param term
     * @return
     */
    public String declToZml(final ZTerm term) {
        final StringWriter sw = new StringWriter();
        final JaxbXmlWriter ozWriter = new JaxbXmlWriter();
        ozWriter.write(term.getTerm(), sw);
        final String result = sw.toString();
        return result.replaceFirst("<\\?xml.*\\?>\\n", "");
//        throw new InstantiationException("ZWrapper cannot be used directly. Use a derived class.");
    }

    public String termToUnicode(final ZTerm term) {
        final StringWriter sw = new StringWriter();
        PrintUtils.print(term.term, sw, (SectionManager) term.sectionInfo,
                DEFAULT_SECTIONNAME, Markup.UNICODE);
        return sw.toString();
    }
    
    public static String getSectionName(){
        return INSTANCE.DEFAULT_SECTIONNAME;
    }

    /**
     * Transforms unicode representation of a Z type definition into a Z term.
     * @param decl
     *          unicode representation of a Z type definition
     * @return
     *          ZTerm representing the type definition
     * @throws ParseException
     *          Occurs when parsing the Z string.
     * @throws InstantiationException
     *          Occurs when calling this method directly. Use subclass instead.
     */
    public ZTerm declToTerm(final String decl) throws ParseException, InstantiationException {
        throw new InstantiationException("ZWrapper cannot be used directly. Use a derived class.");
    }
    
    
}
