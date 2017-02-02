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
package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.CaseStudy;

import org.w3c.dom.Document;

import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.PEAJ2UPPAALConverter;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.PEAXML2JConverter;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.XMLWriter;

/**
 * @author Roland Meyer
 *
 *         Computes the parallel composition of all PEAs in the case study. Class is a prototype only. Path is given as
 *         a constant.
 */
public class CaseStudy {

	// private static final String PATH = "file:/home/roland/Desktop/Workspace/";
	private static final String PATH = "C:/Documents and Settings/oea1lr/My Documents/Test/PEA/peatoolkit-0.89b-src/";

	public static void main(final String[] args) {

		try {
			final PEAXML2JConverter xml2jconverter = new PEAXML2JConverter(false);
			PhaseEventAutomata[] systemPeas =
					xml2jconverter.convert(CaseStudy.PATH + "src/pea/modelchecking/CaseStudy/Environment.xml");
			PhaseEventAutomata toUppaal = systemPeas[0];
			for (int i = 1; i < systemPeas.length; i++) {
				toUppaal = toUppaal.parallel(systemPeas[i]);
			}
			systemPeas = xml2jconverter.convert(CaseStudy.PATH + "src/pea/modelchecking/CaseStudy/TrainEmergency.xml");
			for (int i = 0; i < systemPeas.length; i++) {
				toUppaal = toUppaal.parallel(systemPeas[i]);
			}
			systemPeas = xml2jconverter.convert(CaseStudy.PATH + "src/pea/modelchecking/CaseStudy/TrainReact.xml");
			for (int i = 0; i < systemPeas.length; i++) {
				toUppaal = toUppaal.parallel(systemPeas[i]);
			}
			systemPeas = xml2jconverter.convert(CaseStudy.PATH + "src/pea/modelchecking/CaseStudy/ComNW.xml");
			for (int i = 0; i < systemPeas.length; i++) {
				toUppaal = toUppaal.parallel(systemPeas[i]);
			}
			systemPeas = xml2jconverter.convert(CaseStudy.PATH + "src/pea/modelchecking/CaseStudy/RBC.xml");
			for (int i = 0; i < systemPeas.length; i++) {
				toUppaal = toUppaal.parallel(systemPeas[i]);
			}
			final PhaseEventAutomata[] propertyPeas =
					xml2jconverter.convert(CaseStudy.PATH + "src/pea/modelchecking/CaseStudy/BothNoEBNet0.xml");
			for (int i = 0; i < propertyPeas.length; i++) {
				toUppaal = toUppaal.parallel(propertyPeas[i]);
			}
			final PEAJ2UPPAALConverter j2uppaalConverter = new PEAJ2UPPAALConverter();
			final PhaseEventAutomata[] toUppaalArray = new PhaseEventAutomata[1];
			toUppaal.dump();
			toUppaalArray[0] = toUppaal;
			final Document uppaalDoc = j2uppaalConverter.convert(toUppaalArray);
			final XMLWriter writer = new XMLWriter();
			writer.writeXMLDocumentToFile(uppaalDoc, "src/pea/modelchecking/CaseStudy/toCheck.xml");
		} catch (final Exception e) {
			e.printStackTrace();
		}
	}

}
