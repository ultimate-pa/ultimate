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
package pea.modelchecking;

import org.apache.log4j.Logger;
import org.apache.log4j.PropertyConfigurator;
import org.apache.xerces.parsers.DOMParser;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import java.io.IOException;
import java.util.Set;
import java.util.TreeSet;

import pea.CounterTrace;
import pea.EventDecision;
import pea.CDD;

/**
 * The class <code>MCTraceXML2JConverter</code> converts a given
 * <code>MCTrace</code> -Element from XML to Java representation.
 * 
 * 
 * @see pea.modelchecking.MCTrace
 * @see <code>ModelCheckForm.xsd</code>
 * 
 * @author Roland Meyer
 * 
 *  
 */
public class MCTraceXML2JConverter {

    private static final String DEFAULT_LOGGER = "MCTraceXML2JConverter";

    private Logger logger = null;

    private DOMParser parser = null;

    private FormulaXML2JConverter formulaConverter = null;

    /**
     * Initialises the MCTraceXML2JConverter object. Takes as parameter a string
     * that defines the loggername for the built in log4j logger. If the string
     * is empty, the default name <code>MCTraceXML2JConverter</code> is used.
     * An application using a MCTraceXML2JConverter object has to make sure that
     * the logger is initialised via
     * <code>PropertyConfigurator.configure()</code>.
     * 
     * @param loggerName
     * @see Logger
     * @see PropertyConfigurator
     */
    public MCTraceXML2JConverter(String loggerName, boolean useZDecision) throws Exception {
        if (loggerName.equals("")) {
            this.logger = Logger
                    .getLogger(MCTraceXML2JConverter.DEFAULT_LOGGER);
        } else {
            this.logger = Logger.getLogger(loggerName);
        }

        this.formulaConverter = new FormulaXML2JConverter(useZDecision);

        this.initialiseParser();
    }

    /**
     * Initialises the MCTraceXML2JConverter object with the default logger.
     */
    public MCTraceXML2JConverter(boolean useZDecision) throws Exception {
        this("",useZDecision);
    }

    /**
     * Initialises the built in Xerces2 DomParser. Parser is set to validate the
     * given XML-File against its schema
     * 
     * @throws org.xml.sax.SAXNotRecognizedException
     *             If the requested string does not match an available feature
     * @throws org.xml.sax.SAXNotSupportedException
     *             If the requested feature cannot be set
     * 
     * @see org.apache.xerces.parsers.DOMParser;
     */
    private void initialiseParser() throws Exception {
        this.parser = new DOMParser();

        this.logger.debug("Trying to set parser feature \""
                + XMLTags.PARSER_VALIDATION_FEATURE + "\"");
        this.parser.setFeature(XMLTags.PARSER_VALIDATION_FEATURE, true);
        this.logger.debug("Setting parser feature \""
                + XMLTags.PARSER_VALIDATION_FEATURE + "\" successful");

        this.logger.debug("Trying to set parser feature \""
                + XMLTags.PARSER_SCHEMA_VALIDATION_FEATURE + "\"");
        this.parser.setFeature(XMLTags.PARSER_SCHEMA_VALIDATION_FEATURE, false);
        this.logger.debug("Setting parser feature \""
                + XMLTags.PARSER_SCHEMA_VALIDATION_FEATURE + "\" successful");

    }

    /**
     * Converts all traces in the given <code>MCForm</code> element
     * <code>mbFormNode</code>. Immediately calls the
     * <code>buildTraceModel</code> method.
     * 
     * @param mcFormNode
     *            Node for which the traces need to be converted
     */
    public MCTrace[] convert(Element mcFormNode) {
        return this.buildTraceModel(mcFormNode);
    }

    /**
     * Parses the given file. The top level XML element is supposed to be an
     * <code>MCForm</code> element. All <code>MCTrace</code> elements inside
     * the model checkable formula are converted to Java.
     * 
     * @param file
     *            The formula to be converted, given as XML-file.
     * @return The array of MCTrace[] objects
     * 
     * @throws SAXException
     *             If the formula does not match its schema, an exception is
     *             raised
     * @throws IOException
     *             If the file is not readable an exception is raised.
     *  
     */
    public MCTrace[] convert(String file) throws SAXException, IOException {
        Document document = this.parse(file);
        return this.buildTraceModel(document.getDocumentElement());
    }

    /**
     * Parses the given file. Throws an exception, if there are parsing errors
     * or if the file cannot be accessed.
     */
    private Document parse(String file) throws SAXException, IOException {
        this.logger.debug("Trying to parse file=\"" + file + "\"");
        this.parser.parse(file);
        this.logger.debug("Parsing file=\"" + file + "\" successful");
        return this.parser.getDocument();
    }

    /**
     * Builds the array of <code>MCTrace</code> objects for a given model
     * checkable formula.
     * 
     * 
     * @param node
     *            The formula the model checkable traces need to be converted
     *            for
     * @return MCTrace[] The array of model checkable traces.
     *  
     */
    private MCTrace[] buildTraceModel(Element node) {
        NodeList mcTraceNodes = node.getElementsByTagName(XMLTags.MCTRACE_TAG);

        int traceCount = mcTraceNodes.getLength();
        this.logger.info("MCTraceCount    = " + traceCount);

        MCTrace[] traces = new MCTrace[traceCount];
        for (int i = 0; i < traceCount; i++) {
            this.logger.info("Trying to build mcTrace " + i);
            traces[i] = this.buildMCTrace((Element) mcTraceNodes.item(i));
            this.logger.info("Building mcTrace " + i + " successful");
        }

        return traces;
    }

    /**
     * Build up a Java <code>MCTrace</code> object for a given
     * <code>MCTrace</code> XML element.
     * 
     * @param node
     *            The given XML element
     * @return MCTrace The corresponding Java object
     */
    private MCTrace buildMCTrace(Element node) {
        MCTrace mcTrace = new MCTrace();

        if (node.hasAttribute(XMLTags.ENTRYSYNC_TAG)) {
            String entrySync = node.getAttribute(XMLTags.ENTRYSYNC_TAG);
            if (entrySync.equals("")) {
                throw new RuntimeException(
                        "Existing entry sync events are not allowed to have empty names");
            }
            mcTrace.setEntrySync(EventDecision.create(entrySync));
            this.logger.info("EntrySync       = " + entrySync);

        }

        NodeList traceNodes = node.getElementsByTagName(XMLTags.TRACE_TAG);
        if (traceNodes.getLength() != 1) {
            throw new RuntimeException("Trace count != 1 is not allowed");
        }
        this.logger.info("Trying to build trace");
        this.buildTrace((Element) traceNodes.item(0), mcTrace);
        this.logger.info("Building trace successful");

        String exitSync = node.getAttribute(XMLTags.EXITSYNC_TAG);
        if (exitSync.equals("")) {
            throw new RuntimeException(
                    "Exit sync events are not allowed to be empty");
        }
        mcTrace.setExitSync(EventDecision.create(exitSync));
        this.logger.info("ExitSync        = " + exitSync);

        return mcTrace;
    }

    /**
     * Builds up a Java <code>CounterTrace</code> object for a given
     * <code>Trace</code> XML element. Also saves the
     * <code>missingEvent</code> s after the last phase.
     * 
     * @param node
     *            The given XML element
     * @return MCTrace The Java object that is currently built up
     */
    private void buildTrace(Element node, MCTrace trace) {
        NodeList children = node.getChildNodes();

        NodeList phaseNodes = node.getElementsByTagName(XMLTags.PHASE_TAG);
        int phaseCount = phaseNodes.getLength();
        if (phaseCount == 0) {
            throw new RuntimeException("A trace with 0 phases is not allowed");
        }
        this.logger.info("PhaseCount      = " + phaseCount);

        CounterTrace.DCPhase[] phases = new CounterTrace.DCPhase[phaseCount];

        int actPhase = 0;
        this.logger.info("Trying to build phase " + actPhase);
        phases[actPhase] = 
	    this.buildPhase(CDD.TRUE, (Element) phaseNodes.item(actPhase));
        this.logger.info("Building phase " + actPhase + " successful");
        actPhase++;

	CDD entryEvents = CDD.TRUE;
        Element actNode = (Element) phaseNodes.item(0);

        int traceElementCounter;
        for (traceElementCounter = 0; traceElementCounter < children
                .getLength()
                && actPhase < phaseCount; traceElementCounter++) {
            if (!children.item(traceElementCounter).getNodeName().equals(
                    XMLTags.PHASE_TAG)
                    && !children.item(traceElementCounter).getNodeName()
                            .equals(XMLTags.EVENT_TAG)) {
                continue;
            }

            if (children.item(traceElementCounter) == phaseNodes.item(0)) {
                continue;
            }
            actNode = (Element) children.item(traceElementCounter);

            String actName = actNode.getNodeName();

            //Add a Phase.
            if (actName.equals(XMLTags.PHASE_TAG)) {
                this.logger.info("Trying to build phase " + actPhase);
                phases[actPhase] = this.buildPhase(entryEvents, actNode);
                this.logger.info("EntryEvents     = " + entryEvents);
                this.logger.info("Building phase " + actPhase + " successful");
		entryEvents = CDD.TRUE;
                actPhase++;
            }
            //Add an Event
            if (actName.equals(XMLTags.EVENT_TAG)) {
		CDD event = EventDecision.create(getNameAttribute(actNode));
                if (this.getSpecAttribute(actNode) == true) {
		    entryEvents = entryEvents.and(event);
                } else {
		    entryEvents = entryEvents.and(event.negate());
                }
            }
        }
        trace.setTrace(new CounterTrace(phases));

        //Process missing events
        CDD missingEvents = CDD.TRUE;
        for (int k = traceElementCounter; k < children.getLength(); k++) {
            if (!children.item(k).getNodeName().equals(XMLTags.EVENT_TAG)) {
                continue;
            }
            actNode = (Element) children.item(k);
            if (this.getSpecAttribute(actNode) == true) {
                missingEvents = missingEvents.and(EventDecision.create(this
                        .getNameAttribute(actNode)));
            } else {
                missingEvents = missingEvents.and(EventDecision.create('/',
                        this.getNameAttribute(actNode)));
            }
        }
        this.logger.info("MissingEvents   = " + missingEvents);
        trace.setMissingEvents(missingEvents);

        boolean spec = this.getSpecAttribute(node);
        trace.setSpec(spec);
        this.logger.info("TraceSpec       = " + spec);

    }

    /**
     * Gives the name of an element. Raises an exception if the name is empty.
     */
    private String getNameAttribute(Element element) {
        String name = element.getAttribute(XMLTags.NAME_Tag);
        if (name.equals("")) {
            throw new RuntimeException("Name is not allowed to be empty");
        }
        return name;
    }

    /**
     * Build up a Java <code>DCPhase</code> object for a given
     * <code>Phase</code> XML element. The use of <code>allowEmpty</code>
     * can be enabled in this method.
     * 
     * @param phaseNode
     *            The given XML phase
     * @return CounterTrace.DCPhase The corresponding Java object
     */
    private CounterTrace.DCPhase buildPhase(CDD entryEvents,
					    Element phaseNode) {
        int boundType = CounterTrace.BOUND_NONE;
        double bound = 0;
        NodeList timeBounds = phaseNode
                .getElementsByTagName(XMLTags.TIMEBOUND_TAG);
        if (timeBounds.getLength() > 1) {
            throw new RuntimeException("Time bound count > 1 is not allowed");
        }
        if (timeBounds.getLength() == 1) {
            Element timeBoundNode = (Element) timeBounds.item(0);
            boundType = this.getOperator(timeBoundNode);
            bound = this.getTimeBound(timeBoundNode);
        }

        NodeList stateInvariantNodes = phaseNode
                .getElementsByTagName(XMLTags.STATEINVARIANT_TAG);
        if (stateInvariantNodes.getLength() != 1) {
            throw new RuntimeException(
                    "Stateinvariant count != 1 is not allowed");
        }
        Element invNode = (Element) stateInvariantNodes.item(0);
        CDD inv = formulaConverter.convert(invNode);

        Set<String> forbidden = new TreeSet<String>();
        NodeList forbiddenEventNodes = phaseNode
                .getElementsByTagName(XMLTags.FORBIDDENEVENT_TAG);
        if (forbiddenEventNodes.getLength() > 0) {
            int forbiddenEventCount = forbiddenEventNodes.getLength();
            for (int i = 0; i < forbiddenEventCount; i++) {
                Element actForbiddenEvent = (Element) forbiddenEventNodes
                        .item(i);
                forbidden.add(this.getNameAttribute(actForbiddenEvent));
            }
        }

        boolean allowEmpty = false;
        if (phaseNode.hasAttribute(XMLTags.ALLOWEMPTY_TAG)) {
            String allowEmpyString = phaseNode
                    .getAttribute(XMLTags.ALLOWEMPTY_TAG);
            if (!allowEmpyString.equals(XMLTags.TRUE_CONST)
                    && !allowEmpyString.equals(XMLTags.FALSE_CONST)) {
                throw new RuntimeException(
                        "AllowEmpty attribute needs to be set to \""
                                + XMLTags.TRUE_CONST + "\" or \""
                                + XMLTags.FALSE_CONST + "\"");
            }
            allowEmpty = Boolean.parseBoolean(allowEmpyString);
        }

        CounterTrace.DCPhase phase = 
	    new CounterTrace.DCPhase(entryEvents, inv, boundType,
				     (int) bound, forbidden, allowEmpty);
        this.logger.info("PhaseBoundType  = " + boundType);
        this.logger.info("PhaseBound      = " + (int) bound);
        this.logger.info("PhaseInvariant  = " + inv);
        this.logger.info("ForbiddenEvents = " + forbidden);
        this.logger.info("AllowEmpty      = " + allowEmpty);
        return phase;

    }

    /**
     * Returns the bound of an element as double
     * 
     * @param timeBound
     *            The XML element
     * @return double The double value
     */
    private double getTimeBound(Element timeBound) {
        String bound = timeBound.getAttribute(XMLTags.BOUND_TAG);
        return (new Double(bound)).doubleValue();
    }

    /**
     * Returns the operator of a XML <code>TimeBound</code> element. Raises an
     * exception if the operator is not valid.
     * 
     * @param timeBound
     *            The XML element with the operator to be returned
     * @return int The number for the operator in the <code>CounterTrace</code>
     *         class.
     */
    private int getOperator(Element timeBound) {
        String op = timeBound.getAttribute(XMLTags.OPERATOR_TAG);
        if (op.equals(XMLTags.GREATEREQUAL_CONST))
            return CounterTrace.BOUND_GREATEREQUAL;
        else if (op.equals(XMLTags.GREATER_CONST))
            return CounterTrace.BOUND_GREATER;
        else if (op.equals(XMLTags.LESS_CONST))
            return CounterTrace.BOUND_LESS;
        else if (op.equals(XMLTags.LESSEQUAL_CONST))
            return CounterTrace.BOUND_LESSEQUAL;
        throw new RuntimeException("Operator needs to be " + "\""
                + XMLTags.GREATEREQUAL_CONST + "\", " + "\""
                + XMLTags.GREATER_CONST + "\", " + "\"" + XMLTags.LESS_CONST
                + "\", or " + "\"" + XMLTags.LESSEQUAL_CONST + "\"");
    }

    /**
     * Returns the spec attribute. Raises an exception if the attribute does not
     * have the value true or false.
     * 
     * @param element
     *            The XML element with spec attribute
     * @return boolean The boolean representation of the spec attribute
     */
    private boolean getSpecAttribute(Element element) {
        String spec = element.getAttribute(XMLTags.SPEC_TAG);
        if (!spec.equals(XMLTags.TRUE_CONST)
                && !spec.equals(XMLTags.FALSE_CONST)) {
            throw new RuntimeException(
                    "Spec value != \"true\" and != \"false\" not allowed");
        }
        return Boolean.valueOf(spec).booleanValue();
    }

    /**
     * Used for testing.
     */
    public static void main(String[] args) {
        PropertyConfigurator
                .configure("/home/roland/Desktop/Arbeit/PUMLaut/Parser/src/LogConfiguration.txt");
        try {
            MCTraceXML2JConverter fileParser = new MCTraceXML2JConverter(false);
            fileParser
                    .convert("file:/home/roland/Desktop/Arbeit/PUMLaut/ModelCheckForm/ModelCheckForm.xml");
        } catch (Exception e) {
            System.out.println("Exception raised");
            e.printStackTrace();
        }

    }
}
