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
package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking;

import java.util.ArrayList;
import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.PEATestAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;

/**
 * This class is another version of SimplifyPEAs. It produces <code>Uppaal</code>-output instead of Phase Event
 * Automata.
 *
 * @author Johannes Faber
 *
 */
public class SimplifyPEAsUppaal extends SimplifyPEAs {

	/**
	 * The main-method applies the simplifying methods from its superclass to the documents gives as parameter. It reads
	 * a Phase Event Automata network and optionally a test formula, builds the parallel product for them and writes the
	 * <code>Uppaal</code>-output to an XML-file. <br>
	 * Note: All paths have to be absolut! <br>
	 * 
	 * @param args
	 *            <code>Usage: input-file [formula-file] output-file [--write-ta testautomaton-file]</code><br>
	 *            <br>
	 *            <code>input-file</code> contains PEA's in the syntax of <code>pea.modelchecking.schemas.PEA.xsd</code>
	 *            <br>
	 *            <code>output-file</code> is the filename for the uppaal-output.<br>
	 *            <code>formula-file</code> optionally specifies a test formula in the format of
	 *            <code>pea.modelchecking.schemas.TestForm.xsd</code><br>
	 *            <code>--write-ta testautomaton-file</code> specifies an output-file for the temporary generated test
	 *            automata.
	 */
	@SuppressWarnings("deprecation")
	public static void main(final String[] args) {
		String inputfile = null;
		String outputfile = null;
		String formulafile = null;
		try {
			if (args.length == 2) {
				inputfile = args[0];
				outputfile = args[1];
			} else if (args.length == 3) {
				inputfile = args[0];
				formulafile = args[1];
				outputfile = args[2];
			} else {
				System.out.println(
				        "Usage: java pea.modelchecking.SimplifyPEAsUppaal " + "input-file [formula-file] output-file ");
				return;
			}

			final PEAJ2XMLConverter converter = new PEAJ2XMLConverter();
			final PEAXML2JConverterWithVarList fileParser = new PEAXML2JConverterWithVarList(false);
			final SimplifyPEAsUppaal simplifier = new SimplifyPEAsUppaal();
			final PhaseEventAutomata[] peas = fileParser.convert(inputfile);
			PEATestAutomaton product = new PEATestAutomaton(peas[0]);

			// Compile model-check formula and generate the appropriate automata.
			if (formulafile != null) {
				final Compiler compiler = new Compiler(ILogger.getLogger(SimplifyPEAsUppaal.DEFAULT_LOGGER),  false);
				final ArrayList<PEATestAutomaton[]> peanetList = compiler.compile(formulafile, "");
				if (peanetList.size() > 1) {
					simplifier.logger
					        .warn("Test automata with more than one PEA networks\n" + "are not supported yet.");
				}
				final PEATestAutomaton[] formulaPEAs = peanetList.get(0);
				if (product != null) {
					for (int i = 0; i < formulaPEAs.length; i++) {
						// identifyImplicitBadStates(formulaPEAs[i],SimplifyPEAs.BADSTATESTRING);
						simplifier.logger.info("Parallel composition with formala-pea.");
						product = product.parallel(formulaPEAs[i]);
					}

				}
			}

			// Build product automaton.
			for (int i = 1; i < peas.length; i++) {
				simplifier.logger.info("Parallel composition pea " + i);
				product = product.parallel(peas[i]);
			}

			simplifier.logger.info("Parallel composition finished.");

			final ArrayList[] variables = fileParser.getAdditionalVariables();
			final ArrayList[] types = fileParser.getTypes();

			// peas = new PhaseEventAutomata[1];
			// peas[0] = product;
			// Merge variables to one list.
			final ArrayList<String> mergedVariables0 = new ArrayList<String>();
			final ArrayList<String> mergedTypes0 = new ArrayList<String>();
			final ArrayList[] mergedVariables = { mergedVariables0 };
			final ArrayList[] mergedTypes = { mergedTypes0 };
			for (int i = 0; i < variables.length; i++) {
				final Iterator typeIter = types[i].iterator();
				for (final Iterator iter = variables[i].iterator(); iter.hasNext();) {
					final String tempName = (String) iter.next();
					final String tempType = (String) typeIter.next();
					if (!mergedVariables[0].contains(tempName)) {
						mergedVariables0.add(tempName);
						mergedTypes0.add(tempType);
					}
				}
			}
			converter.setAdditionalVariables(mergedVariables);
			converter.setAdditionalTypes(mergedTypes);

			product = simplifier.mergeFinalLocations(product, SimplifyPEAs.BADSTATESTRING);

			simplifier.logger.info("Merge transitions.");
			simplifier.mergeTransitions(product);
			simplifier.logger.info("Finished.");

			// simplifier.logger.info("Starting conversion to XML.");
			// Document result = converter.convert(peas);
			// simplifier.logger.info("Finished.");
			simplifier.logger.info("Convert to DNF.");
			final J2UPPAALWriter uppaalWriter = new J2UPPAALWriter();
			uppaalWriter.writePEA2UppaalFile(outputfile, product);
			simplifier.logger.info("Finished.");

			// Formula2DNFCompiler dnfCompiler = new Formula2DNFCompiler();
			//
			// dnfCompiler.compile(result);
			// simplifier.logger.info("Finished.");
			//
			// ///Replace all ORs in guards with additional transitions
			// simplifier.logger.info("Resolving ORs.");
			// NodeList transitions = result.getElementsByTagName(XMLTags.TRANSITION_TAG);
			// int transitionCount = transitions.getLength();
			// ArrayList<Node> removeList = new ArrayList<Node>();
			// for (int i = 0; i < transitionCount; i++) {
			// ArrayList<Element> newTransitions = simplifier.eliminateORs((Element) transitions.item(i));
			// if(newTransitions != null){
			// Node transitionsNode = transitions.item(i).getParentNode();
			// removeList.add(transitions.item(i));
			// for (Element transition : newTransitions) {
			// Node newTrans = result.importNode(transition, true);
			// transitionsNode.appendChild(newTrans);
			// }
			// }
			// }
			// for (Node node : removeList) {
			// Node parent = node.getParentNode();
			// parent.removeChild(node);
			// }
			// simplifier.logger.info("Finished.");
			//
			// XMLWriter writer = new XMLWriter();
			// writer.writeXMLDocumentToFile(result, "./temp.xml");
			// PEAXML2JConverter convi = new PEAXML2JConverter();
			// peas=convi.convert("./temp.xml");
			//
			// PEAJ2UPPAALConverter j2uppaalConverter = new PEAJ2UPPAALConverter();
			//
			// Document uppaalDoc = j2uppaalConverter.convert(peas);
			// writer.writeXMLDocumentToFile(uppaalDoc,
			// outputfile);

		} catch (final Exception e) {
			e.printStackTrace();
		}
	}

}
