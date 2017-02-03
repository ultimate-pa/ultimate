/* $Id: CaseStudyToTCS.java 326 2008-08-01 16:41:13Z jfaber $ 
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
package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.CaseStudy;

import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.PEA2TCSJ2XMLConverter;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.PEAXML2JConverter;


/**
 * @author Roland Meyer
 *
 * Computes the parallel composition of all PEAs in the case study.
 * Class is a prototype only.
 * Path is given as a constant.
 */
public class CaseStudyToTCS {

    private static final String PATH = "./";

    public static void main(String[] args) {
        try {
            final PEAXML2JConverter xml2jconverter = new PEAXML2JConverter(false);
            PhaseEventAutomata[] systemPeas = xml2jconverter
                    .convert(CaseStudyToTCS.PATH
                            + "pea/modelchecking/CaseStudy/Environment.xml");
            PhaseEventAutomata toTCS = systemPeas[0];
            for (int i = 1; i < systemPeas.length; i++) {
                toTCS = toTCS.parallel(systemPeas[i]);
            }
            systemPeas = xml2jconverter.convert(CaseStudyToTCS.PATH
                    + "pea/modelchecking/CaseStudy/TrainEmergency.xml");
            for (int i = 0; i < systemPeas.length; i++) {
                toTCS = toTCS.parallel(systemPeas[i]);
            }
            systemPeas = xml2jconverter.convert(CaseStudyToTCS.PATH
                    + "pea/modelchecking/CaseStudy/TrainReact.xml");
            for (int i = 0; i < systemPeas.length; i++) {
                toTCS = toTCS.parallel(systemPeas[i]);
            }
            systemPeas = xml2jconverter.convert(CaseStudyToTCS.PATH
                    + "pea/modelchecking/CaseStudy/ComNW.xml");
            for (int i = 0; i < systemPeas.length; i++) {
                toTCS = toTCS.parallel(systemPeas[i]);
            }
            systemPeas = xml2jconverter.convert(CaseStudyToTCS.PATH
                    + "pea/modelchecking/CaseStudy/RBC.xml");
            for (int i = 0; i < systemPeas.length; i++) {
                toTCS = toTCS.parallel(systemPeas[i]);
            }
            final PhaseEventAutomata[] propertyPeas = xml2jconverter
                    .convert(CaseStudyToTCS.PATH
                            + "pea/modelchecking/CaseStudy/BothNoEBNet0.xml");
            for (int i = 0; i < propertyPeas.length; i++) {
                toTCS = toTCS.parallel(propertyPeas[i]);
            }
            final PEA2TCSJ2XMLConverter pea2tcsConverter = new PEA2TCSJ2XMLConverter();
            final PhaseEventAutomata[] toTCSArray = new PhaseEventAutomata[1];
            toTCS.dump();
            toTCSArray[0] = toTCS;
            pea2tcsConverter.convert(toTCSArray, "pea/modelchecking/CaseStudy/toCheckAsTCS.xml", false);
        } catch (final Exception e) {
            e.printStackTrace();
        }
    }
}
