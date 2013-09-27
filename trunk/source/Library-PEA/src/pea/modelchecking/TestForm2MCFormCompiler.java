/* Id: TestForm2MCFormCompiler.java 160 2006-03-08 14:45:19Z hoenicke $ 
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

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.apache.log4j.Logger;
import org.apache.log4j.PropertyConfigurator;
import org.apache.xerces.parsers.DOMParser;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import pea.PhaseEventAutomata;

/**
 * Creates the model checkable representation (conform to
 * <code>ModelCheckForm.xsd</code>) of a test formula given as XML file valid
 * in respect to <code>TestForm.xsd</code>. Writes several results during the
 * compilation to help the user understand the single steps in the compilation
 * process and to make the compilation traceable.
 * 
 * Extends the abstract class <code>Formula2NFCompiler</code> to give access
 * to the basic normal form compilation algorithms.
 * 
 * @see pea.modelchecking.Formula2NFCompiler
 * @see <code>TestForm.xsd</code>
 * @see <code>ModelCheckForm.xsd</code>
 * 
 * @author Roland Meyer
 *  
 */
public class TestForm2MCFormCompiler extends Formula2NFCompiler {

    protected static final String DEFAULT_LOGGER = "TestForm2MCFormCompiler";

    protected DOMParser parser = null;

    private List<Element> mcFormsList = null;
    private List<Element> trueNodeList = null;
    private List<String> handledIntervalsList = null;

    private int syncEventCounter = 0;

    /**
     * Initialises the TestForm2MCFormCompiler object. Takes as parameter a
     * string that defines the loggername for the built in log4j logger. If the
     * string is empty, the default name <code>TestForm2MCFormCompiler</code>
     * is used. An application using a TestForm2MCFormCompiler object has to
     * make sure that the logger is initialised via
     * <code>PropertyConfigurator.configure()</code>.
     * 
     * @param loggerName
     * @see Logger
     * @see PropertyConfigurator
     */
    public TestForm2MCFormCompiler(String loggerName) throws Exception {
        URL url = getClass().getResource(PhaseEventAutomata.LOGCONFIGFILE);
        PropertyConfigurator.configure(url);

        if (loggerName.equals("")) {
            this.logger = Logger
                    .getLogger(TestForm2MCFormCompiler.DEFAULT_LOGGER);
        } else {
            this.logger = Logger.getLogger(loggerName);
        }

        this.initialiseParser();

        this.trueNodeList = new ArrayList<Element>();
        this.mcFormsList = new ArrayList<Element>();
        this.handledIntervalsList = new ArrayList<String>();
    }

    /**
     * Initialises the TestForm2MCFormCompiler object with the default logger.
     */
    public TestForm2MCFormCompiler() throws Exception {
        this("");
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
    protected void initialiseParser() throws Exception {
        this.parser = new DOMParser();

        this.logger.debug("Trying to set parser feature \""
                + XMLTags.PARSER_VALIDATION_FEATURE + "\"");
        this.parser.setFeature(XMLTags.PARSER_VALIDATION_FEATURE, true);
        this.logger.debug("Setting parser feature \""
                + XMLTags.PARSER_VALIDATION_FEATURE + "\" successful");

        this.logger.debug("Trying to set parser feature \""
                + XMLTags.PARSER_SCHEMA_VALIDATION_FEATURE + "\"");
        this.parser.setFeature(XMLTags.PARSER_SCHEMA_VALIDATION_FEATURE, true);
        this.logger.debug("Setting parser feature \""
                + XMLTags.PARSER_SCHEMA_VALIDATION_FEATURE + "\" successful");

    }

    /**
     * Parses the given file. Throws an SAXException, if the file is not correct
     * in respect to its schema. Throws an IOException if the file cannot be
     * accessed.
     */
    protected Document parse(String file) throws SAXException, IOException {
        this.logger.debug("Trying to parse file=\"" + file + "\"");
        this.parser.parse(file);
        this.logger.debug("Parsing file=\"" + file + "\" successful");
        return this.parser.getDocument();
    }

    /**
     * Calls the other compile method with an empty string as second parameter.
     */
    public Document compile(String toCompile) throws Exception {
        return this.compile(toCompile, "");
    }

    /**
     * Returns the <code>ModelCheckForm.xsd</code> conform representation of
     * the given <code>TestForm.xsd</code> conform file <code>toCompile</code>.
     * The model checkable representation is saved in the file
     * <code>mcFile</code>.
     * 
     * @param toCompile
     *            The formula to be compiled to model checkable form.
     * @param mcFile
     *            The file where the model checkable representation needs to be
     *            saved. If the string is empty, a default file is taken.
     * 
     * @return Document The XML document conform to
     *         <code>ModelCheckForm.xsd</code>
     * 
     * @throws SAXException
     *             If the formula does not match its schema, an exception is
     *             raised
     * @throws IOException
     *             If the file is not readable an exception is raised.
     * 
     * @see <code>ModelCheckForm.xsd</code>
     * @see <code>TestForm.xsd</code>
     */
    public Document compile(String toCompile, String mcFile) throws Exception {

        this.document = this.parse(toCompile);

        this.mcFormsList.clear();
        this.trueNodeList.clear();
        this.handledIntervalsList.clear();

        File ioFile = new File(toCompile);
        String fileName = ioFile.getName();
        String fileNameWithoutXML = ioFile.getName().substring(0,
                fileName.length() - 4);
	String parent = ioFile.getParent() != null ? ioFile.getParent()+ "/" : "";
        String binFile = parent + fileNameWithoutXML
                + "_bin.xml";
        String syncFile = parent + fileNameWithoutXML
                + "_sync.xml";
        String nfFile = parent + fileNameWithoutXML
                + "_nf.xml";
        if (mcFile.equals("")) {
            mcFile = parent + fileNameWithoutXML + "_mc.xml";
        }

        this.logger.info("Starting compilation");

        NodeList testForms = this.document
                .getElementsByTagName(XMLTags.TESTFORM_TAG);
        if (testForms.getLength() != 1) {
            throw new RuntimeException("Testform count != 1 is not allowed");
        }
        Element testForm = (Element) testForms.item(0);

        this.logger.info("Trying to make testForm tree binary");
        this.makeBinary(testForm);
        this.logger.info("Making testForm tree binary successful");

        XMLWriter writer = new XMLWriter();
        writer.writeXMLDocumentToFile(this.document, binFile);

        this.logger.info("Trying to replace chops with sync events");
        this.introduceSyncEvents();
        this.logger.info("Replacing chops with sync events successful");

        writer.writeXMLDocumentToFile(this.document, syncFile);

        this.logger.info("Trying to build normal form");
        this.buildNF(testForm);
        this.logger.info("Building normal form successful");

        writer.writeXMLDocumentToFile(this.document, nfFile);

        this.logger.info("Trying to build model-checkable form");
        this.findMCForms(testForm);
        this.appendMCForms();
        this.logger.info("Building model-checkable form successful");

        writer.writeXMLDocumentToFile(this.document, mcFile);

        this.logger.info("Compilation finished");
        return this.document;
    }

    /**
     * Generates a list of all <code>MCForm</code> elements.
     */
    private void appendMCForms() {
        if (!this.mcFormsList.isEmpty()) {
            Element mcFormsNode = this.document
                    .createElement(XMLTags.MCFORMS_TAG);
            mcFormsNode.setAttribute(XMLTags.XMLNS_TAG, XMLTags.SCHEMAINST_TAG);
            mcFormsNode.setAttribute(XMLTags.NONAMESPACELOC_TAG,
                    XMLTags.MODELCHECKFORMSCHEMA_PATH);

            Iterator mcFormIterator = this.mcFormsList.iterator();
            while (mcFormIterator.hasNext()) {
                Element actMCFormNode = (Element) mcFormIterator.next();
                mcFormsNode.appendChild(actMCFormNode);
            }

            this.document.replaceChild(mcFormsNode, this.document
                    .getFirstChild());
        } else {
            throw new RuntimeException("The list of mcForms is empty");
        }
    }

    /**
     * Replaces CHOP operators by sync events.
     *  
     */
    protected void introduceSyncEvents() {
        NodeList tfTreeNodes = this.document
                .getElementsByTagName(XMLTags.TFTREE_TAG);
        int tfTreeNodeCount = tfTreeNodes.getLength();
        for (int i = 0; i < tfTreeNodeCount; i++) {
            Element actTfTreeNode = (Element) tfTreeNodes.item(i);
            if (actTfTreeNode.getAttribute(XMLTags.OPERATOR_TAG).equals(
                    XMLTags.CHOP_CONST)) {
                actTfTreeNode.setAttribute(XMLTags.OPERATOR_TAG, this
                        .getFreshSyncEvent());
            }
        }
    }

    /**
     * Creates a new true DC-phase
     */
    private Element getNewTrueNode() {
        Element trueNode = this.document.createElement(XMLTags.TRACE_TAG);
        trueNode.setAttribute(XMLTags.SPEC_TAG, XMLTags.TRUE_CONST);

        Element phase = this.document.createElement(XMLTags.PHASE_TAG);

        Element stateInvariant = this.document
                .createElement(XMLTags.STATEINVARIANT_TAG);
        Element booleanExpression = this.document
                .createElement(XMLTags.BOOLEANEXPRESSION_TAG);
        booleanExpression.setAttribute(XMLTags.EXPRESSION_TAG,
                XMLTags.TRUE_CONST);
        stateInvariant.appendChild(booleanExpression);

        phase.appendChild(stateInvariant);
        trueNode.appendChild(phase);

        this.trueNodeList.add(trueNode);
        return trueNode;
    }

    /**
     * Implements the special distributivity between Sync and AND
     */
    protected void changeNodeSyncChildAnd(Element node, Element[] children,
            int childIndex) {
        Element[] andChildren = this.getFormulaOperands(children[childIndex]);
        String syncEvent = node.getAttribute(XMLTags.OPERATOR_TAG);

        Element syncNode1 = this.document.createElement(XMLTags.TFTREE_TAG);
        syncNode1.setAttribute(XMLTags.OPERATOR_TAG, syncEvent);
        Element syncNode2 = this.document.createElement(XMLTags.TFTREE_TAG);
        syncNode2.setAttribute(XMLTags.OPERATOR_TAG, syncEvent);
        Element syncNode3 = this.document.createElement(XMLTags.TFTREE_TAG);
        syncNode3.setAttribute(XMLTags.OPERATOR_TAG, syncEvent);

        children[childIndex].appendChild(syncNode1);
        children[childIndex].appendChild(syncNode2);

        if (childIndex == 0) {
            syncNode1.appendChild(andChildren[0]);
            syncNode1.appendChild(this.getNewTrueNode());

            syncNode2.appendChild(andChildren[1]);
            syncNode2.appendChild(this.getNewTrueNode());

            syncNode3.appendChild(this.getNewTrueNode());
            syncNode3.appendChild(children[1]);

            node.appendChild(syncNode3);

        } else {
            syncNode1.appendChild(this.getNewTrueNode());
            syncNode1.appendChild(andChildren[0]);

            syncNode2.appendChild(this.getNewTrueNode());
            syncNode2.appendChild(andChildren[1]);

            syncNode3.appendChild(children[0]);
            syncNode3.appendChild(this.getNewTrueNode());

            node.insertBefore(syncNode3, children[1]);
        }
        node.setAttribute(XMLTags.OPERATOR_TAG, XMLTags.AND_CONST);
    }

    /**
     * Testformulae may not have NOT operators. Thus the call of this method
     * raises an exception.
     */
    protected void changeNodeNotChildAnd(Element node, Element child) {
        throw new RuntimeException("Operator " + XMLTags.NOT_CONST
                + " may not be used in testformulae");
    }

    /**
     * Testformulae may not have NOT operators. Thus the call of this method
     * raises an exception.
     */
    protected void changeNodeNotChildOr(Element node, Element child) {
        throw new RuntimeException("Operator " + XMLTags.NOT_CONST
                + " may not be used in testformulae");
    }

    /**
     * Splits up the given formula tree in model checkable form. For each
     * disjunct a <code>MCForm</code> element is generated. Recursive
     * algorithm.
     * 
     * @param actNode
     *            The node to be inspected for disjuncts.
     */
    protected void findMCForms(Node actNode) {
        if (actNode.getNodeType() != Node.ELEMENT_NODE) {
            this.logger.debug("No element node, returning...");
            return;
        }
        Element node = (Element) actNode;

        if (node.getNodeName().equals(XMLTags.TESTFORM_TAG)) {
            this.logger.debug("TestForm node, finding mcForm in children...");
            NodeList childList = node.getChildNodes();
            for (int i = 0; i < childList.getLength(); i++) {
                this.findMCForms(childList.item(i));
            }
            this.logger.debug("TestForm node, "
                    + "finding mcForm in children finished, " + "returning...");
            return;
        }

        if (node.getAttribute(XMLTags.OPERATOR_TAG).equals(XMLTags.OR_CONST)) {
            this.logger.debug(XMLTags.OR_CONST
                    + "-node, finding mcForm in children...");
            Element[] operands = this.getFormulaOperands(node);
            for (int i = 0; i < operands.length; i++) {
                this.findMCForms(operands[i]);
            }
            this.logger.debug(XMLTags.OR_CONST + "-node, "
                    + "finding mcForm in children finished, " + "returning...");
        } else {
            this.logger.debug("Building mcForm...");
            this.createMCForm(node);
            this.logger.debug("Building mcForm finished, returning...");
        }
    }

    /**
     * Creates an <code>MCForm</code> element for a disjunct found in the
     * tree. The disjunct is given by its root element.
     * 
     * @param node
     *            The root element of the disjunct which needs to be converted
     *            from <code>TestForm.xsd</code> to
     *            <code>ModelCheckForm.xsd</code> representation.
     * 
     * @see <code>TestForm.xsd</code>
     * @see <code>ModelCheckForm.xsd</code>
     */
    protected void createMCForm(Element node) {
        ArrayList<Element> mcTraceNodeList = new ArrayList<Element>();
        String commonExitSync = this.getFreshSyncEvent();

        if (node.getNodeName().equals(XMLTags.TRACE_TAG)) {
            this.logger.debug("Building mcForm from single trace node...");
            Element mcTraceNode = this.createMCTrace(node, commonExitSync);
            if (mcTraceNode != null) {
                mcTraceNodeList.add(mcTraceNode);
            }
            this.logger.debug("Building mcForm from single trace node "
                    + "finished...");
        } else {

            this.logger.debug("Building mcForm from several trace nodes...");

            //True traces are treated afterwards to omit superfluous
            //mcTrace nodes
            ArrayList<Element> trueTraces = new ArrayList<Element>();

            NodeList traces = node.getElementsByTagName(XMLTags.TRACE_TAG);
            int traceCount = traces.getLength();
            for (int i = 0; i < traceCount; i++) {
                Element actTrace = (Element) traces.item(i);
                if (this.isTrueNode(actTrace)) {
                    trueTraces.add(actTrace);
                } else {
                    Element mcTraceNode = this.createMCTrace(actTrace,
                            commonExitSync);
                    if (mcTraceNode != null) {
                        mcTraceNodeList.add(mcTraceNode);
                    }
                }
            }

            Iterator trueTracesIterator = trueTraces.iterator();
            while (trueTracesIterator.hasNext()) {
                Element actTrace = (Element) trueTracesIterator.next();
                Element mcTraceNode = this.createMCTrace(actTrace,
                        commonExitSync);
                if (mcTraceNode != null) {
                    mcTraceNodeList.add(mcTraceNode);
                }
            }

            this.logger.debug("Building mcForm from several trace nodes "
                    + "finished...");
        }

        if (!mcTraceNodeList.isEmpty()) {
            Element mcFormNode = this.document
                    .createElement(XMLTags.MCFORM_TAG);
            Iterator mcTraceNodeIterator = mcTraceNodeList.iterator();
            while (mcTraceNodeIterator.hasNext()) {
                Element actMCTraceNode = (Element) mcTraceNodeIterator.next();
                mcFormNode.appendChild(actMCTraceNode);
            }

            this.mcFormsList.add(mcFormNode);
        }
    }

    /**
     * Creates an <code>MCTrace</code> element for a trace in the model
     * checkable representation of a test formula.
     * 
     * @param trace
     *            The <code>Trace</code> element to be converted
     * @param commonExitSync
     *            The exit sync of the trace
     * 
     * @return Element The corresponding <code>MCTrace</code> element.
     * 
     * @see <code>TestForm.xsd</code>
     * @see <code>ModelCheckForm.xsd</code>
     *  
     */
    protected Element createMCTrace(Element trace, String commonExitSync) {
        Element parentNode1 = (Element) trace.getParentNode();
        Element parentNode2 = null;
        if (!parentNode1.getNodeName().equals(XMLTags.TESTFORM_TAG)) {
            parentNode2 = (Element) parentNode1.getParentNode();
        }
        boolean traceIsFirstChild = this.isFirstChild(trace);
        boolean parentNode1IsFirstChild;
        if (parentNode2 != null) {
            parentNode1IsFirstChild = this.isFirstChild(parentNode1);
        } else {
            parentNode1IsFirstChild = true;
        }
        String syncEvent1 = null;
        String syncEvent2 = null;

        if (parentNode1.getAttribute(XMLTags.OPERATOR_TAG).startsWith(
                XMLTags.SYNC_PREFIX)) {
            syncEvent1 = parentNode1.getAttribute(XMLTags.OPERATOR_TAG);
        }
        if (parentNode2 != null) {
            if (parentNode2.getAttribute(XMLTags.OPERATOR_TAG).startsWith(
                    XMLTags.SYNC_PREFIX)) {
                syncEvent2 = parentNode2.getAttribute(XMLTags.OPERATOR_TAG);
            }
        }

        if (syncEvent1 == null) {
            this.logger.debug("SyncEvent1==null");
            if (this.isTrueNode(trace)) {
                return null;
            }
            return this.getMCTraceNode((Element) trace.cloneNode(true), null,
                    commonExitSync);
        }
        if (traceIsFirstChild) {
            if (syncEvent2 == null || parentNode1IsFirstChild) {
                this.logger.debug("traceIsFirstChild && "
                        + "(syncEvent2==NULL || parentNode1IsFirstChild");
                if (this.isTrueNode(trace)) {
                    return null;
                }
                return this.getMCTraceNode((Element) trace.cloneNode(true),
                        null, syncEvent1);
            } else {
                this.logger.debug("traceIsFirstChild && "
                        + "(syncEvent2!=NULL && !parentNode1IsFirstChild");
                if (this.isAlreadyHandled(syncEvent2, syncEvent1)
                        && this.isTrueNode(trace)) {
                    return null;
                }
                return this.getMCTraceNode((Element) trace.cloneNode(true),
                        syncEvent2, syncEvent1);
            }
        } else {
            if (syncEvent2 == null || !parentNode1IsFirstChild) {
                this.logger.debug("!traceIsFirstChild && "
                        + "(syncEvent2==NULL || parentNode1IsFirstChild");
                if (this.isTrueNode(trace)) {
                    return null;
                }
                return this.getMCTraceNode((Element) trace.cloneNode(true),
                        syncEvent1, commonExitSync);
            } else {
                this.logger.debug("!traceIsFirstChild && "
                        + "(syncEvent2!=NULL && parentNode1IsFirstChild");
                if (this.isAlreadyHandled(syncEvent1, syncEvent2)
                        && this.isTrueNode(trace)) {
                    return null;
                }
                return this.getMCTraceNode((Element) trace.cloneNode(true),
                        syncEvent1, syncEvent2);
            }
        }
    }

    /**
     * Delivers a fresh sync event
     */
    private String getFreshSyncEvent() {
        String result = XMLTags.SYNC_PREFIX + this.syncEventCounter;
        this.syncEventCounter++;
        return result;
    }

    /**
     * Creates an <code>MCTrace</code> node with the given parameters
     * 
     * @param traceNode
     *            The trace node of the <code>MCTrace</code> element
     * @param entrySync
     *            The entry sync event
     * @param exitSync
     *            The exit sync event
     * @return Element The generated <code>MCTrace</code> element.
     * 
     * @see <code>TestForm.xsd</code>
     * @see <code>ModelCheckForm.xsd</code>
     */
    protected Element getMCTraceNode(Element traceNode, String entrySync,
            String exitSync) {
        Element mcTraceNode = this.document.createElement(XMLTags.MCTRACE_TAG);

        if (entrySync != null) {
            if (entrySync.equals("")) {
                throw new RuntimeException("Existing entry sync events "
                        + "are not allowed to be empty");
            }
            mcTraceNode.setAttribute(XMLTags.ENTRYSYNC_TAG, entrySync);
        }

        if (exitSync.equals("")) {
            throw new RuntimeException(
                    "Exit sync events are not allowed to be empty");
        }
        mcTraceNode.setAttribute(XMLTags.EXITSYNC_TAG, exitSync);
        mcTraceNode.appendChild(traceNode);

        this.handledIntervalsList.add(entrySync + exitSync);
        return mcTraceNode;
    }

    private boolean isTrueNode(Element traceNode) {
        return this.trueNodeList.contains(traceNode);
    }

    private boolean isAlreadyHandled(String sync1, String sync2) {
        return this.handledIntervalsList.contains(sync1 + sync2);
    }

    private boolean isFirstChild(Node node) {
        Element parent = (Element) node.getParentNode();
        Element[] operands = this.getFormulaOperands(parent);
        if (node == operands[0]) {
            return true;
        }
        return false;
    }

    /**
     * Implements the inherited methods with correct XML-Tags
     */
    protected Element getNewTreeElement() {
        return this.document.createElement(XMLTags.TFTREE_TAG);
    }

    protected boolean isTreeElement(Node node) {
        return node.getNodeName().equals(XMLTags.TFTREE_TAG);
    }

    protected boolean isBasicElement(Node node) {
        return node.getNodeName().equals(XMLTags.TRACE_TAG);
    }

    protected boolean isFormulaElement(Node node) {
        return node.getNodeName().equals(XMLTags.TESTFORM_TAG);
    }

    protected boolean isCorrectOperator(String operator) {
        return operator.equals(XMLTags.OR_CONST)
                || operator.equals(XMLTags.AND_CONST)
                || operator.equals(XMLTags.CHOP_CONST)
                || operator.startsWith(XMLTags.SYNC_PREFIX);
    }
}
