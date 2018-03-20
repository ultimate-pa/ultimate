/* $Id: MCTraceXML2JConverter.java 399 2009-06-26 16:01:20Z jfaber $
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
import java.util.Set;
import java.util.TreeSet;

import org.apache.xerces.parsers.DOMParser;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;

/**
 * The class <code>MCTraceXML2JConverter</code> converts a given <code>MCTrace</code> -Element from XML to Java
 * representation.
 *
 *
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.MCTrace
 * @see <code>ModelCheckForm.xsd</code>
 *
 * @author Roland Meyer
 *
 *
 */
public class MCTraceXML2JConverter {

	private static final String DEFAULT_LOGGER = "MCTraceXML2JConverter";

	private ILogger logger = null;

	private DOMParser parser = null;

	private FormulaXML2JConverter formulaConverter = null;

	/**
	 * Initialises the MCTraceXML2JConverter object. Takes as parameter a string that defines the loggername for the
	 * built in log4j logger. If the string is empty, the default name <code>MCTraceXML2JConverter</code> is used. An
	 * application using a MCTraceXML2JConverter object has to make sure that the logger is initialised via
	 * <code>PropertyConfigurator.configure()</code>.
	 *
	 * @param loggerName
	 * @see ILogger
	 * @see PropertyConfigurator
	 */
	public MCTraceXML2JConverter(final String loggerName, final boolean useZDecision) throws Exception {
		if (loggerName.equals("")) {
			logger = ILogger.getLogger(MCTraceXML2JConverter.DEFAULT_LOGGER);
		} else {
			logger = ILogger.getLogger(loggerName);
		}

		formulaConverter = new FormulaXML2JConverter(useZDecision);

		initialiseParser();
	}

	/**
	 * Initialises the MCTraceXML2JConverter object with the default logger.
	 */
	public MCTraceXML2JConverter(final boolean useZDecision) throws Exception {
		this("", useZDecision);
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
	private void initialiseParser() throws Exception {
		parser = new DOMParser();

		logger.debug("Trying to set parser feature \"" + XMLTags.PARSER_VALIDATION_FEATURE + "\"");
		parser.setFeature(XMLTags.PARSER_VALIDATION_FEATURE, true);
		logger.debug("Setting parser feature \"" + XMLTags.PARSER_VALIDATION_FEATURE + "\" successful");

		logger.debug("Trying to set parser feature \"" + XMLTags.PARSER_SCHEMA_VALIDATION_FEATURE + "\"");
		parser.setFeature(XMLTags.PARSER_SCHEMA_VALIDATION_FEATURE, false);
		logger.debug("Setting parser feature \"" + XMLTags.PARSER_SCHEMA_VALIDATION_FEATURE + "\" successful");

	}

	/**
	 * Converts all traces in the given <code>MCForm</code> element <code>mbFormNode</code>. Immediately calls the
	 * <code>buildTraceModel</code> method.
	 *
	 * @param mcFormNode
	 *            Node for which the traces need to be converted
	 */
	public MCTrace[] convert(final Element mcFormNode) {
		return buildTraceModel(mcFormNode);
	}

	/**
	 * Parses the given file. The top level XML element is supposed to be an <code>MCForm</code> element. All
	 * <code>MCTrace</code> elements inside the model checkable formula are converted to Java.
	 *
	 * @param file
	 *            The formula to be converted, given as XML-file.
	 * @return The array of MCTrace[] objects
	 *
	 * @throws SAXException
	 *             If the formula does not match its schema, an exception is raised
	 * @throws IOException
	 *             If the file is not readable an exception is raised.
	 *
	 */
	public MCTrace[] convert(final String file) throws SAXException, IOException {
		final Document document = parse(file);
		return buildTraceModel(document.getDocumentElement());
	}

	/**
	 * Parses the given file. Throws an exception, if there are parsing errors or if the file cannot be accessed.
	 */
	private Document parse(final String file) throws SAXException, IOException {
		logger.debug("Trying to parse file=\"" + file + "\"");
		parser.parse(file);
		logger.debug("Parsing file=\"" + file + "\" successful");
		return parser.getDocument();
	}

	/**
	 * Builds the array of <code>MCTrace</code> objects for a given model checkable formula.
	 *
	 *
	 * @param node
	 *            The formula the model checkable traces need to be converted for
	 * @return MCTrace[] The array of model checkable traces.
	 *
	 */
	private MCTrace[] buildTraceModel(final Element node) {
		final NodeList mcTraceNodes = node.getElementsByTagName(XMLTags.MCTRACE_TAG);

		final int traceCount = mcTraceNodes.getLength();
		logger.info("MCTraceCount    = " + traceCount);

		final MCTrace[] traces = new MCTrace[traceCount];
		for (int i = 0; i < traceCount; i++) {
			logger.info("Trying to build mcTrace " + i);
			traces[i] = buildMCTrace((Element) mcTraceNodes.item(i));
			logger.info("Building mcTrace " + i + " successful");
		}

		return traces;
	}

	/**
	 * Build up a Java <code>MCTrace</code> object for a given <code>MCTrace</code> XML element.
	 *
	 * @param node
	 *            The given XML element
	 * @return MCTrace The corresponding Java object
	 */
	private MCTrace buildMCTrace(final Element node) {
		final MCTrace mcTrace = new MCTrace();

		if (node.hasAttribute(XMLTags.ENTRYSYNC_TAG)) {
			final String entrySync = node.getAttribute(XMLTags.ENTRYSYNC_TAG);
			if (entrySync.equals("")) {
				throw new RuntimeException("Existing entry sync events are not allowed to have empty names");
			}
			mcTrace.setEntrySync(EventDecision.create(entrySync));
			logger.info("EntrySync       = " + entrySync);

		}

		final NodeList traceNodes = node.getElementsByTagName(XMLTags.TRACE_TAG);
		if (traceNodes.getLength() != 1) {
			throw new RuntimeException("Trace count != 1 is not allowed");
		}
		logger.info("Trying to build trace");
		buildTrace((Element) traceNodes.item(0), mcTrace);
		logger.info("Building trace successful");

		final String exitSync = node.getAttribute(XMLTags.EXITSYNC_TAG);
		if (exitSync.equals("")) {
			throw new RuntimeException("Exit sync events are not allowed to be empty");
		}
		mcTrace.setExitSync(EventDecision.create(exitSync));
		logger.info("ExitSync        = " + exitSync);

		return mcTrace;
	}

	/**
	 * Builds up a Java <code>CounterTrace</code> object for a given <code>Trace</code> XML element. Also saves the
	 * <code>missingEvent</code> s after the last phase.
	 *
	 * @param node
	 *            The given XML element
	 * @return MCTrace The Java object that is currently built up
	 */
	private void buildTrace(final Element node, final MCTrace trace) {
		final NodeList children = node.getChildNodes();

		final NodeList phaseNodes = node.getElementsByTagName(XMLTags.PHASE_TAG);
		final int phaseCount = phaseNodes.getLength();
		if (phaseCount == 0) {
			throw new RuntimeException("A trace with 0 phases is not allowed");
		}
		logger.info("PhaseCount      = " + phaseCount);

		final CounterTrace.DCPhase[] phases = new CounterTrace.DCPhase[phaseCount];

		int actPhase = 0;
		logger.info("Trying to build phase " + actPhase);
		phases[actPhase] = buildPhase(CDD.TRUE, (Element) phaseNodes.item(actPhase));
		logger.info("Building phase " + actPhase + " successful");
		actPhase++;

		CDD entryEvents = CDD.TRUE;
		Element actNode = (Element) phaseNodes.item(0);

		int traceElementCounter;
		for (traceElementCounter = 0; traceElementCounter < children.getLength()
		        && actPhase < phaseCount; traceElementCounter++) {
			if (!children.item(traceElementCounter).getNodeName().equals(XMLTags.PHASE_TAG)
			        && !children.item(traceElementCounter).getNodeName().equals(XMLTags.EVENT_TAG)) {
				continue;
			}

			if (children.item(traceElementCounter) == phaseNodes.item(0)) {
				continue;
			}
			actNode = (Element) children.item(traceElementCounter);

			final String actName = actNode.getNodeName();

			// Add a Phase.
			if (actName.equals(XMLTags.PHASE_TAG)) {
				logger.info("Trying to build phase " + actPhase);
				phases[actPhase] = buildPhase(entryEvents, actNode);
				logger.info("EntryEvents     = " + entryEvents);
				logger.info("Building phase " + actPhase + " successful");
				entryEvents = CDD.TRUE;
				actPhase++;
			}
			// Add an Event
			if (actName.equals(XMLTags.EVENT_TAG)) {
				final CDD event = EventDecision.create(getNameAttribute(actNode));
				if (getSpecAttribute(actNode)) {
					entryEvents = entryEvents.and(event);
				} else {
					entryEvents = entryEvents.and(event.negate());
				}
			}
		}
		trace.setTrace(new CounterTrace(phases));

		// Process missing events
		CDD missingEvents = CDD.TRUE;
		for (int k = traceElementCounter; k < children.getLength(); k++) {
			if (!children.item(k).getNodeName().equals(XMLTags.EVENT_TAG)) {
				continue;
			}
			actNode = (Element) children.item(k);
			if (getSpecAttribute(actNode)) {
				missingEvents = missingEvents.and(EventDecision.create(getNameAttribute(actNode)));
			} else {
				missingEvents = missingEvents.and(EventDecision.createNeg(getNameAttribute(actNode)));
			}
		}
		logger.info("MissingEvents   = " + missingEvents);
		trace.setMissingEvents(missingEvents);

		final boolean spec = getSpecAttribute(node);
		trace.setSpec(spec);
		logger.info("TraceSpec       = " + spec);

	}

	/**
	 * Gives the name of an element. Raises an exception if the name is empty.
	 */
	private static String getNameAttribute(final Element element) {
		final String name = element.getAttribute(XMLTags.NAME_Tag);
		if (name.equals("")) {
			throw new RuntimeException("Name is not allowed to be empty");
		}
		return name;
	}

	/**
	 * Build up a Java <code>DCPhase</code> object for a given <code>Phase</code> XML element. The use of
	 * <code>allowEmpty</code> can be enabled in this method.
	 *
	 * @param phaseNode
	 *            The given XML phase
	 * @return CounterTrace.DCPhase The corresponding Java object
	 */
	private CounterTrace.DCPhase buildPhase(final CDD entryEvents, final Element phaseNode) {
		int boundType = CounterTrace.BOUND_NONE;
		double bound = 0;
		final NodeList timeBounds = phaseNode.getElementsByTagName(XMLTags.TIMEBOUND_TAG);
		if (timeBounds.getLength() > 1) {
			throw new RuntimeException("Time bound count > 1 is not allowed");
		}
		if (timeBounds.getLength() == 1) {
			final Element timeBoundNode = (Element) timeBounds.item(0);
			boundType = getOperator(timeBoundNode);
			bound = getTimeBound(timeBoundNode);
		}

		final NodeList stateInvariantNodes = phaseNode.getElementsByTagName(XMLTags.STATEINVARIANT_TAG);
		if (stateInvariantNodes.getLength() != 1) {
			throw new RuntimeException("Stateinvariant count != 1 is not allowed");
		}
		final Element invNode = (Element) stateInvariantNodes.item(0);
		final CDD inv = formulaConverter.convert(invNode);

		final Set<String> forbidden = new TreeSet<>();
		final NodeList forbiddenEventNodes = phaseNode.getElementsByTagName(XMLTags.FORBIDDENEVENT_TAG);
		if (forbiddenEventNodes.getLength() > 0) {
			final int forbiddenEventCount = forbiddenEventNodes.getLength();
			for (int i = 0; i < forbiddenEventCount; i++) {
				final Element actForbiddenEvent = (Element) forbiddenEventNodes.item(i);
				forbidden.add(getNameAttribute(actForbiddenEvent));
			}
		}

		boolean allowEmpty = false;
		if (phaseNode.hasAttribute(XMLTags.ALLOWEMPTY_TAG)) {
			final String allowEmpyString = phaseNode.getAttribute(XMLTags.ALLOWEMPTY_TAG);
			if (!allowEmpyString.equals(XMLTags.TRUE_CONST) && !allowEmpyString.equals(XMLTags.FALSE_CONST)) {
				throw new RuntimeException("AllowEmpty attribute needs to be set to \"" + XMLTags.TRUE_CONST
				        + "\" or \"" + XMLTags.FALSE_CONST + "\"");
			}
			allowEmpty = Boolean.parseBoolean(allowEmpyString);
		}

		final CounterTrace.DCPhase phase = new CounterTrace.DCPhase(entryEvents, inv, boundType, (int) bound, forbidden,
		        allowEmpty);
		logger.info("PhaseBoundType  = " + boundType);
		logger.info("PhaseBound      = " + (int) bound);
		logger.info("PhaseInvariant  = " + inv);
		logger.info("ForbiddenEvents = " + forbidden);
		logger.info("AllowEmpty      = " + allowEmpty);
		return phase;

	}

	/**
	 * Returns the bound of an element as double
	 *
	 * @param timeBound
	 *            The XML element
	 * @return double The double value
	 */
	private static double getTimeBound(final Element timeBound) {
		final String bound = timeBound.getAttribute(XMLTags.BOUND_TAG);
		return (new Double(bound)).doubleValue();
	}

	/**
	 * Returns the operator of a XML <code>TimeBound</code> element. Raises an exception if the operator is not valid.
	 *
	 * @param timeBound
	 *            The XML element with the operator to be returned
	 * @return int The number for the operator in the <code>CounterTrace</code> class.
	 */
	private static int getOperator(final Element timeBound) {
		final String op = timeBound.getAttribute(XMLTags.OPERATOR_TAG);
		if (op.equals(XMLTags.GREATEREQUAL_CONST)) {
			return CounterTrace.BOUND_GREATEREQUAL;
		} else if (op.equals(XMLTags.GREATER_CONST)) {
			return CounterTrace.BOUND_GREATER;
		} else if (op.equals(XMLTags.LESS_CONST)) {
			return CounterTrace.BOUND_LESS;
		} else if (op.equals(XMLTags.LESSEQUAL_CONST)) {
			return CounterTrace.BOUND_LESSEQUAL;
		}
		throw new RuntimeException(
		        "Operator needs to be " + "\"" + XMLTags.GREATEREQUAL_CONST + "\", " + "\"" + XMLTags.GREATER_CONST
		                + "\", " + "\"" + XMLTags.LESS_CONST + "\", or " + "\"" + XMLTags.LESSEQUAL_CONST + "\"");
	}

	/**
	 * Returns the spec attribute. Raises an exception if the attribute does not have the value true or false.
	 *
	 * @param element
	 *            The XML element with spec attribute
	 * @return boolean The boolean representation of the spec attribute
	 */
	private static boolean getSpecAttribute(final Element element) {
		final String spec = element.getAttribute(XMLTags.SPEC_TAG);
		if (!spec.equals(XMLTags.TRUE_CONST) && !spec.equals(XMLTags.FALSE_CONST)) {
			throw new RuntimeException("Spec value != \"true\" and != \"false\" not allowed");
		}
		return Boolean.parseBoolean(spec);
	}

	/**
	 * Used for testing.
	 */
	public static void main(final String[] args) {
		try {
			final MCTraceXML2JConverter fileParser = new MCTraceXML2JConverter(false);
			fileParser.convert("file:/home/roland/Desktop/Arbeit/PUMLaut/ModelCheckForm/ModelCheckForm.xml");
		} catch (final Exception e) {
			System.out.println("Exception raised");
			e.printStackTrace();
		}

	}
}
