/* $Id: PEAXML2JConverter.java 326 2008-08-01 16:41:13Z jfaber $
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

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.xerces.parsers.DOMParser;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;

/**
 *
 * Converts a given XML file which is valid in respect to <code>PEA.xsd</code> into an array of
 * <code>PhaseEventAutomata</code> objects. The Java objects correspond to the PEAs in the file.
 *
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.FormulaXML2JConverter
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata
 * @see <code>PEA.xsd</code>
 *
 * @author Roland Meyer
 *
 */
public class PEAXML2JConverter {

	protected static final String DEFAULT_LOGGER = "PEAXML2JConverter";

	protected ILogger logger = null;

	protected DOMParser parser = null;

	protected FormulaXML2JConverter formulaConverter = null;

	// Flag to choose whether booleanDecision or ZDecision should be generated from a formula
	protected boolean useZDecision = false;

	/**
	 * Initialises the PEAXML2JConverter object. Takes as parameter a string that defines the loggername for the built
	 * in log4j logger. If the string is empty, the default name <code>PEAXML2JConverter</code> is used. An application
	 * using a PEAXML2JConverter object has to make sure that the logger is initialised via
	 * <code>PropertyConfigurator.configure()</code>.
	 *
	 * @param loggerName
	 * @see ILogger
	 * @see PropertyConfigurator
	 */
	public PEAXML2JConverter(final String loggerName, final boolean useZ) throws Exception {
		if (loggerName.equals("")) {
			logger = ILogger.getLogger(PEAXML2JConverter.DEFAULT_LOGGER);
		} else {
			logger = ILogger.getLogger(loggerName);
		}

		formulaConverter = new FormulaXML2JConverter(useZ);

		initialiseParser();
	}

	/**
	 * Initialises the PEAXML2JConverter object with the default logger.
	 */
	public PEAXML2JConverter(final boolean useZ) throws Exception {
		this("", useZ);
	}

	/**
	 * Initialises the built in Xerces2 DomParser. Parser is set to validate the given XML-File against its schema
	 *
	 * @throws org.xml.sax.SAXNotRecognizedException
	 *             If the requested string does not match an available feature
	 * @throws org.xml.sax.SAXNotSupportedException
	 *             If the requested feature cannot be set
	 *
	 * @see org.apache.xerces.parsers.DOMParser;
	 */
	protected void initialiseParser() throws Exception {
		parser = new DOMParser();

		logger.debug("Trying to set parser feature \"" + XMLTags.PARSER_VALIDATION_FEATURE + "\"");
		parser.setFeature(XMLTags.PARSER_VALIDATION_FEATURE, true);
		logger.debug("Setting parser feature \"" + XMLTags.PARSER_VALIDATION_FEATURE + "\" successful");

		logger.debug("Trying to set parser feature \"" + XMLTags.PARSER_SCHEMA_VALIDATION_FEATURE + "\"");
		parser.setFeature(XMLTags.PARSER_SCHEMA_VALIDATION_FEATURE, false);
		logger.debug("Setting parser feature \"" + XMLTags.PARSER_SCHEMA_VALIDATION_FEATURE + "\" successful");

	}

	/**
	 * Converts a net of phase event automata given as XML file valid in respect to <code>PEA.xsd</code>. Returns an
	 * array of <code>PhaseEventAutomata</code> objects corresponding to the PEAs inside the net.
	 *
	 * @param file
	 *            The net of phase event automata to be converted
	 * @return PhaseEventAutomata[] The array of PEAs in the net
	 *
	 * @throws SAXException
	 *             If the file is not valid in respect to its schema
	 * @throws IOException
	 *             If the file is not accessible
	 *
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata
	 * @see <code>PEA.xsd</code>
	 */
	public PhaseEventAutomata[] convert(final String file) throws SAXException, IOException {
		final Document document = parse(file);

		final NodeList peaNodes = document.getElementsByTagName(XMLTags.PEA_TAG);
		final int peaCount = peaNodes.getLength();
		if (peaCount == 0) {
			throw new RuntimeException("PEA count = 0 is not allowed");
		}

		final PhaseEventAutomata[] peas = new PhaseEventAutomata[peaCount];
		for (int i = 0; i < peaCount; i++) {
			final Element actPEANode = (Element) peaNodes.item(i);
			logger.info("Trying to build pea " + i);
			peas[i] = createPhaseEventAutomaton(actPEANode);
			logger.info("Building pea " + i + " successful");
		}

		return peas;
	}

	/**
	 * Parses the given XML file. Raises a SAXException if the file is not valid in respect to its schema. Throws an
	 * IOException if the file is not accessible.
	 */
	protected Document parse(final String file) throws SAXException, IOException {
		// this.parser.parse(this.getClass().getClassLoader().getResource(file).toString());
		parser.parse(file);
		return parser.getDocument();
	}

	/**
	 * Creates a Java <code>PhaseEventAutomata</code> object for the given XML <code>PEA</code> element.
	 *
	 * @param peaNode
	 *            The phase event automaton to be converted
	 * @return CDD The Java representation of the PEA
	 *
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.Phase
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.Transition
	 * @see <code>PEA.xsd</code>
	 */

	protected PhaseEventAutomata createPhaseEventAutomaton(final Element peaNode) {
		final NodeList phaseNodes = peaNode.getElementsByTagName(XMLTags.PHASE_TAG);
		final int phaseCount = phaseNodes.getLength();
		if (phaseCount == 0) {
			throw new RuntimeException("Phase count = 0 is not allowed");
		}

		final HashMap<String, Phase> phases = new HashMap<>();
		final HashMap<String, Phase> initialPhases = new HashMap<>();

		// Get Clocks
		final NodeList clockNodes = peaNode.getElementsByTagName(XMLTags.CLOCK_TAG);
		final ArrayList<String> peaClocks = new ArrayList<>();
		final int clockNodeCount = clockNodes.getLength();
		for (int i = 0; i < clockNodeCount; i++) {
			final Element actClockNode = (Element) clockNodes.item(i);
			final String actClock = actClockNode.getAttribute(XMLTags.NAME_Tag);
			peaClocks.add(actClock);
		}

		// Get Variables
		final NodeList variableNodes = peaNode.getElementsByTagName(XMLTags.VARIABLE_TAG);
		final Map<String, String> variablesForPEA = new HashMap<>();
		for (int i = 0; i < variableNodes.getLength(); i++) {
			final Element node = (Element) variableNodes.item(i);
			final String varName = node.getAttribute("name");
			final String type = node.getAttribute("type");
			variablesForPEA.put(varName, type);
		}

		// Get Variables
		final NodeList eventNodes = peaNode.getElementsByTagName(XMLTags.EVENT_TAG);
		final Set<String> eventsForPEA = new HashSet<>();
		for (int i = 0; i < eventNodes.getLength(); i++) {
			final Element node = (Element) eventNodes.item(i);
			final String eventName = node.getAttribute("name");
			eventsForPEA.add(eventName);
		}

		// Build Java phases
		for (int i = 0; i < phaseCount; i++) {
			final Element actPhaseNode = (Element) phaseNodes.item(i);
			logger.info("Trying to build phase " + i);
			final Phase actPhase = createJavaPhase(actPhaseNode);
			logger.info("Building phase " + i + " successful");
			phases.put(actPhase.getName(), actPhase);
			if (actPhaseNode.hasAttribute(XMLTags.INITIAL_TAG)) {
				if (actPhaseNode.getAttribute(XMLTags.INITIAL_TAG).equals(XMLTags.TRUE_CONST)) {
					initialPhases.put(actPhase.getName(), actPhase);
				}
			}
		}

		// Build Java transitions
		final NodeList transitionNodes = peaNode.getElementsByTagName(XMLTags.TRANSITION_TAG);
		final int transitionCount = transitionNodes.getLength();
		for (int i = 0; i < transitionCount; i++) {
			final Element actTransitionNode = (Element) transitionNodes.item(i);
			logger.info("Trying to build transition " + i);
			createJavaTransition(actTransitionNode, phases);
			logger.info("Building transition " + i + " successful");
		}

		final Phase[] phasesArray = phases.values().toArray(new Phase[phases.size()]);
		final Phase[] initPhasesArray = initialPhases.values().toArray(new Phase[initialPhases.size()]);
		final String peaName = getNameAttribute(peaNode);
		final PhaseEventAutomata pea = new PhaseEventAutomata(peaName, phasesArray, initPhasesArray, peaClocks,
				variablesForPEA, eventsForPEA, null);
		return pea;
	}

	/**
	 * Returns the name attribute. Raises an exception if the name is empty.
	 */
	private static String getNameAttribute(final Element node) {
		final String name = node.getAttribute(XMLTags.NAME_Tag);
		if (name.equals("")) {
			throw new RuntimeException("Empty name attributes are not allowed");
		}
		return name;
	}

	/**
	 * Creates a Java <code>Transition</code> object for the given XML <code>Transition</code> element.
	 *
	 * @param transitionNode
	 *            The transition to be converted
	 * @param phases
	 *            The transition is saved within its source phase.
	 *
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.Phase
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.Transition
	 * @see <code>PEA.xsd</code>
	 */
	protected void createJavaTransition(final Element transitionNode, final Map<String, Phase> phases) {
		final NodeList resetNodes = transitionNode.getElementsByTagName(XMLTags.RESET_TAG);
		final int resetNodeCount = resetNodes.getLength();
		final String[] resets = new String[resetNodeCount];
		for (int i = 0; i < resetNodeCount; i++) {
			resets[i] = getNameAttribute((Element) resetNodes.item(i));
			logger.info("resets[" + i + "]=" + resets[i]);
		}

		final NodeList guardNode = transitionNode.getElementsByTagName(XMLTags.GUARD_TAG);
		if (guardNode.getLength() != 1) {
			throw new RuntimeException("Guard node count != 1 not allowed");
		}
		final CDD guard = formulaConverter.convert((Element) guardNode.item(0));
		logger.info("guard=" + guard);

		final String sourceName = transitionNode.getAttribute(XMLTags.SOURCE_TAG);
		if (sourceName.equals("")) {
			throw new RuntimeException("Source attribute is not allowed to be empty");
		}
		final Phase sourcePhase = phases.get(sourceName);
		logger.info("source=" + sourceName);

		final String targetName = transitionNode.getAttribute(XMLTags.TARGET_TAG);
		if (targetName.equals("")) {
			throw new RuntimeException("Target attribute is not allowed to be empty");
		}
		final Phase targetPhase = phases.get(targetName);
		logger.info("target=" + targetName);

		sourcePhase.addTransition(targetPhase, guard, resets);
	}

	/**
	 * Creates a Java object for the given <code>Phase</code> element.
	 *
	 * @param phaseNode
	 *            The phase to be converted
	 * @return CDD The Java representation of the phase
	 */
	protected Phase createJavaPhase(final Element phaseNode) {
		final String name = getNameAttribute(phaseNode);
		logger.info("name=" + name);

		final NodeList invariantNodes = phaseNode.getElementsByTagName(XMLTags.INVARIANT_TAG);
		if (invariantNodes.getLength() != 1) {
			throw new RuntimeException("Invariant node count != 1 is not allowed");
		}
		final CDD invariant = formulaConverter.convert((Element) invariantNodes.item(0));
		logger.info("invariant=" + invariant);

		final CDD clockInvariant = createClockInvariant(phaseNode);
		logger.info("clockInvariant=" + clockInvariant);

		final Phase result = new Phase(name, invariant, clockInvariant);
		return result;
	}

	/**
	 * Calls the <code>FormulaXML2JConverter</code> to convert the clockinvariant of the given phase element.
	 *
	 * @param phaseNode
	 *            The phase the clockinvariant needs to be converted for.
	 * @return CDD The Java representation of the clock invariant
	 *
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.FormulaXML2JConverter
	 */
	protected CDD createClockInvariant(final Element phaseNode) {
		CDD clockInvariant = CDD.TRUE;
		final NodeList clockInvariantNodes = phaseNode.getElementsByTagName(XMLTags.CLOCKINVARIANT_TAG);
		if (clockInvariantNodes.getLength() > 1) {
			throw new RuntimeException("Clockinvariant node count > 1 is not allowed");
		}
		if (clockInvariantNodes.getLength() == 1) {
			clockInvariant = clockInvariant.and(formulaConverter.convert((Element) clockInvariantNodes.item(0)));
		}

		return clockInvariant;
	}

	/**
	 * Used for testing.
	 */
	public static void main(final String[] args) {
		try {
			final PEAXML2JConverter fileParser = new PEAXML2JConverter(false);
			final PhaseEventAutomata[] output = fileParser.convert("./pea/modelchecking/CaseStudy/Property0_par.xml");
			final PhaseEventAutomata[] irgendwann = fileParser.convert("./pea/modelchecking/CaseStudy/ComNW.xml");
			// PEAJ2UPPAALConverter converter = new PEAJ2UPPAALConverter();
			// PhaseEventAutomata[] array = new PhaseEventAutomata[1];
			// output[0].dump();
			// irgendwann[1].dump();
			final PhaseEventAutomata newAut = output[0].parallel(irgendwann[1]).parallel(irgendwann[1]);
			newAut.dump();
			// output[0].parallel(irgendwann[0]).dump();
			// array[0] = output[0].parallel(irgendwann[0]);
			// array[0] = irgendwann[0].parallel(output[0]);
			// array[0].dump();
			// Document uppaal = converter.convert(array);
			// XMLWriter writer = new XMLWriter();
			// writer.writeXMLDocumentToFile(uppaal,
			// "src/pea/modelchecking/example/toCheck.xml");
		} catch (final Exception e) {
			e.printStackTrace();
		}
	}

}
