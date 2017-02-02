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
package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.apache.xerces.parsers.DOMParser;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Creates the model checkable representation (conform to <code>ModelCheckForm.xsd</code>) of a test formula given as
 * XML file valid in respect to <code>TestForm.xsd</code>. Writes several results during the compilation to help the
 * user understand the single steps in the compilation process and to make the compilation traceable.
 *
 * Extends the abstract class <code>Formula2NFCompiler</code> to give access to the basic normal form compilation
 * algorithms.
 *
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.Formula2NFCompiler
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
	 * Initialises the TestForm2MCFormCompiler object. Takes as parameter a string that defines the loggername for the
	 * built in log4j logger. If the string is empty, the default name <code>TestForm2MCFormCompiler</code> is used. An
	 * application using a TestForm2MCFormCompiler object has to make sure that the logger is initialised via
	 * <code>PropertyConfigurator.configure()</code>.
	 * 
	 * @param loggerName
	 * @see ILogger
	 * @see PropertyConfigurator
	 */
	public TestForm2MCFormCompiler(final String loggerName) throws Exception {
		if (loggerName.equals("")) {
			logger = ILogger.getLogger(TestForm2MCFormCompiler.DEFAULT_LOGGER);
		} else {
			logger = ILogger.getLogger(loggerName);
		}

		initialiseParser();

		trueNodeList = new ArrayList<>();
		mcFormsList = new ArrayList<>();
		handledIntervalsList = new ArrayList<>();
	}

	/**
	 * Initialises the TestForm2MCFormCompiler object with the default logger.
	 */
	public TestForm2MCFormCompiler() throws Exception {
		this("");
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
		parser.setFeature(XMLTags.PARSER_SCHEMA_VALIDATION_FEATURE, true);
		logger.debug("Setting parser feature \"" + XMLTags.PARSER_SCHEMA_VALIDATION_FEATURE + "\" successful");

	}

	/**
	 * Parses the given file. Throws an SAXException, if the file is not correct in respect to its schema. Throws an
	 * IOException if the file cannot be accessed.
	 */
	protected Document parse(final String file) throws SAXException, IOException {
		logger.debug("Trying to parse file=\"" + file + "\"");
		parser.parse(file);
		logger.debug("Parsing file=\"" + file + "\" successful");
		return parser.getDocument();
	}

	/**
	 * Calls the other compile method with an empty string as second parameter.
	 */
	public Document compile(final String toCompile) throws Exception {
		return this.compile(toCompile, "");
	}

	/**
	 * Returns the <code>ModelCheckForm.xsd</code> conform representation of the given <code>TestForm.xsd</code> conform
	 * file <code>toCompile</code>. The model checkable representation is saved in the file <code>mcFile</code>.
	 * 
	 * @param toCompile
	 *            The formula to be compiled to model checkable form.
	 * @param mcFile
	 *            The file where the model checkable representation needs to be saved. If the string is empty, a default
	 *            file is taken.
	 * 
	 * @return Document The XML document conform to <code>ModelCheckForm.xsd</code>
	 * 
	 * @throws SAXException
	 *             If the formula does not match its schema, an exception is raised
	 * @throws IOException
	 *             If the file is not readable an exception is raised.
	 * 
	 * @see <code>ModelCheckForm.xsd</code>
	 * @see <code>TestForm.xsd</code>
	 */
	public Document compile(final String toCompile, String mcFile) throws Exception {

		document = parse(toCompile);

		mcFormsList.clear();
		trueNodeList.clear();
		handledIntervalsList.clear();

		final File ioFile = new File(toCompile);
		final String fileName = ioFile.getName();
		final String fileNameWithoutXML = ioFile.getName().substring(0, fileName.length() - 4);
		final String parent = ioFile.getParent() != null ? ioFile.getParent() + "/" : "";
		final String binFile = parent + fileNameWithoutXML + "_bin.xml";
		final String syncFile = parent + fileNameWithoutXML + "_sync.xml";
		final String nfFile = parent + fileNameWithoutXML + "_nf.xml";
		if (mcFile.equals("")) {
			mcFile = parent + fileNameWithoutXML + "_mc.xml";
		}

		logger.info("Starting compilation");

		final NodeList testForms = document.getElementsByTagName(XMLTags.TESTFORmTAG);
		if (testForms.getLength() != 1) {
			throw new RuntimeException("Testform count != 1 is not allowed");
		}
		final Element testForm = (Element) testForms.item(0);

		logger.info("Trying to make testForm tree binary");
		makeBinary(testForm);
		logger.info("Making testForm tree binary successful");

		final XMLWriter writer = new XMLWriter();
		writer.writeXMLDocumentToFile(document, binFile);

		logger.info("Trying to replace chops with sync events");
		introduceSyncEvents();
		logger.info("Replacing chops with sync events successful");

		writer.writeXMLDocumentToFile(document, syncFile);

		logger.info("Trying to build normal form");
		buildNF(testForm);
		logger.info("Building normal form successful");

		writer.writeXMLDocumentToFile(document, nfFile);

		logger.info("Trying to build model-checkable form");
		findMCForms(testForm);
		appendMCForms();
		logger.info("Building model-checkable form successful");

		writer.writeXMLDocumentToFile(document, mcFile);

		logger.info("Compilation finished");
		return document;
	}

	/**
	 * Generates a list of all <code>MCForm</code> elements.
	 */
	private void appendMCForms() {
		if (!mcFormsList.isEmpty()) {
			final Element mcFormsNode = document.createElement(XMLTags.MCFORMS_TAG);
			mcFormsNode.setAttribute(XMLTags.XMLNS_TAG, XMLTags.SCHEMAINST_TAG);
			mcFormsNode.setAttribute(XMLTags.NONAMESPACELOC_TAG, XMLTags.MODELCHECKFORMSCHEMA_PATH);

			final Iterator<Element> mcFormIterator = mcFormsList.iterator();
			while (mcFormIterator.hasNext()) {
				final Element actMCFormNode = mcFormIterator.next();
				mcFormsNode.appendChild(actMCFormNode);
			}

			document.replaceChild(mcFormsNode, document.getFirstChild());
		} else {
			throw new RuntimeException("The list of mcForms is empty");
		}
	}

	/**
	 * Replaces CHOP operators by sync events.
	 * 
	 */
	protected void introduceSyncEvents() {
		final NodeList tfTreeNodes = document.getElementsByTagName(XMLTags.TFTREE_TAG);
		final int tfTreeNodeCount = tfTreeNodes.getLength();
		for (int i = 0; i < tfTreeNodeCount; i++) {
			final Element actTfTreeNode = (Element) tfTreeNodes.item(i);
			if (actTfTreeNode.getAttribute(XMLTags.OPERATOR_TAG).equals(XMLTags.CHOP_CONST)) {
				actTfTreeNode.setAttribute(XMLTags.OPERATOR_TAG, getFreshSyncEvent());
			}
		}
	}

	/**
	 * Creates a new true DC-phase
	 */
	private Element getNewTrueNode() {
		final Element trueNode = document.createElement(XMLTags.TRACE_TAG);
		trueNode.setAttribute(XMLTags.SPEC_TAG, XMLTags.TRUE_CONST);

		final Element phase = document.createElement(XMLTags.PHASE_TAG);

		final Element stateInvariant = document.createElement(XMLTags.STATEINVARIANT_TAG);
		final Element booleanExpression = document.createElement(XMLTags.BOOLEANEXPRESSION_TAG);
		booleanExpression.setAttribute(XMLTags.EXPRESSION_TAG, XMLTags.TRUE_CONST);
		stateInvariant.appendChild(booleanExpression);

		phase.appendChild(stateInvariant);
		trueNode.appendChild(phase);

		trueNodeList.add(trueNode);
		return trueNode;
	}

	/**
	 * Implements the special distributivity between Sync and AND
	 */
	@Override
	protected void changeNodeSyncChildAnd(final Element node, final Element[] children, final int childIndex) {
		final Element[] andChildren = getFormulaOperands(children[childIndex]);
		final String syncEvent = node.getAttribute(XMLTags.OPERATOR_TAG);

		final Element syncNode1 = document.createElement(XMLTags.TFTREE_TAG);
		syncNode1.setAttribute(XMLTags.OPERATOR_TAG, syncEvent);
		final Element syncNode2 = document.createElement(XMLTags.TFTREE_TAG);
		syncNode2.setAttribute(XMLTags.OPERATOR_TAG, syncEvent);
		final Element syncNode3 = document.createElement(XMLTags.TFTREE_TAG);
		syncNode3.setAttribute(XMLTags.OPERATOR_TAG, syncEvent);

		children[childIndex].appendChild(syncNode1);
		children[childIndex].appendChild(syncNode2);

		if (childIndex == 0) {
			syncNode1.appendChild(andChildren[0]);
			syncNode1.appendChild(getNewTrueNode());

			syncNode2.appendChild(andChildren[1]);
			syncNode2.appendChild(getNewTrueNode());

			syncNode3.appendChild(getNewTrueNode());
			syncNode3.appendChild(children[1]);

			node.appendChild(syncNode3);

		} else {
			syncNode1.appendChild(getNewTrueNode());
			syncNode1.appendChild(andChildren[0]);

			syncNode2.appendChild(getNewTrueNode());
			syncNode2.appendChild(andChildren[1]);

			syncNode3.appendChild(children[0]);
			syncNode3.appendChild(getNewTrueNode());

			node.insertBefore(syncNode3, children[1]);
		}
		node.setAttribute(XMLTags.OPERATOR_TAG, XMLTags.AND_CONST);
	}

	/**
	 * Testformulae may not have NOT operators. Thus the call of this method raises an exception.
	 */
	@Override
	protected void changeNodeNotChildAnd(final Element node, final Element child) {
		throw new RuntimeException("Operator " + XMLTags.NOT_CONST + " may not be used in testformulae");
	}

	/**
	 * Testformulae may not have NOT operators. Thus the call of this method raises an exception.
	 */
	@Override
	protected void changeNodeNotChildOr(final Element node, final Element child) {
		throw new RuntimeException("Operator " + XMLTags.NOT_CONST + " may not be used in testformulae");
	}

	/**
	 * Splits up the given formula tree in model checkable form. For each disjunct a <code>MCForm</code> element is
	 * generated. Recursive algorithm.
	 * 
	 * @param actNode
	 *            The node to be inspected for disjuncts.
	 */
	protected void findMCForms(final Node actNode) {
		if (actNode.getNodeType() != Node.ELEMENT_NODE) {
			logger.debug("No element node, returning...");
			return;
		}
		final Element node = (Element) actNode;

		if (node.getNodeName().equals(XMLTags.TESTFORmTAG)) {
			logger.debug("TestForm node, finding mcForm in children...");
			final NodeList childList = node.getChildNodes();
			for (int i = 0; i < childList.getLength(); i++) {
				findMCForms(childList.item(i));
			}
			logger.debug("TestForm node, " + "finding mcForm in children finished, " + "returning...");
			return;
		}

		if (node.getAttribute(XMLTags.OPERATOR_TAG).equals(XMLTags.OR_CONST)) {
			logger.debug(XMLTags.OR_CONST + "-node, finding mcForm in children...");
			final Element[] operands = getFormulaOperands(node);
			for (int i = 0; i < operands.length; i++) {
				findMCForms(operands[i]);
			}
			logger.debug(XMLTags.OR_CONST + "-node, " + "finding mcForm in children finished, " + "returning...");
		} else {
			logger.debug("Building mcForm...");
			createMCForm(node);
			logger.debug("Building mcForm finished, returning...");
		}
	}

	/**
	 * Creates an <code>MCForm</code> element for a disjunct found in the tree. The disjunct is given by its root
	 * element.
	 * 
	 * @param node
	 *            The root element of the disjunct which needs to be converted from <code>TestForm.xsd</code> to
	 *            <code>ModelCheckForm.xsd</code> representation.
	 * 
	 * @see <code>TestForm.xsd</code>
	 * @see <code>ModelCheckForm.xsd</code>
	 */
	protected void createMCForm(final Element node) {
		final ArrayList<Element> mcTraceNodeList = new ArrayList<>();
		final String commonExitSync = getFreshSyncEvent();

		if (node.getNodeName().equals(XMLTags.TRACE_TAG)) {
			logger.debug("Building mcForm from single trace node...");
			final Element mcTraceNode = createMCTrace(node, commonExitSync);
			if (mcTraceNode != null) {
				mcTraceNodeList.add(mcTraceNode);
			}
			logger.debug("Building mcForm from single trace node " + "finished...");
		} else {

			logger.debug("Building mcForm from several trace nodes...");

			// True traces are treated afterwards to omit superfluous
			// mcTrace nodes
			final ArrayList<Element> trueTraces = new ArrayList<>();

			final NodeList traces = node.getElementsByTagName(XMLTags.TRACE_TAG);
			final int traceCount = traces.getLength();
			for (int i = 0; i < traceCount; i++) {
				final Element actTrace = (Element) traces.item(i);
				if (isTrueNode(actTrace)) {
					trueTraces.add(actTrace);
				} else {
					final Element mcTraceNode = createMCTrace(actTrace, commonExitSync);
					if (mcTraceNode != null) {
						mcTraceNodeList.add(mcTraceNode);
					}
				}
			}

			final Iterator<Element> trueTracesIterator = trueTraces.iterator();
			while (trueTracesIterator.hasNext()) {
				final Element actTrace = trueTracesIterator.next();
				final Element mcTraceNode = createMCTrace(actTrace, commonExitSync);
				if (mcTraceNode != null) {
					mcTraceNodeList.add(mcTraceNode);
				}
			}

			logger.debug("Building mcForm from several trace nodes " + "finished...");
		}

		if (!mcTraceNodeList.isEmpty()) {
			final Element mcFormNode = document.createElement(XMLTags.MCFORmTAG);
			final Iterator<Element> mcTraceNodeIterator = mcTraceNodeList.iterator();
			while (mcTraceNodeIterator.hasNext()) {
				final Element actMCTraceNode = mcTraceNodeIterator.next();
				mcFormNode.appendChild(actMCTraceNode);
			}

			mcFormsList.add(mcFormNode);
		}
	}

	/**
	 * Creates an <code>MCTrace</code> element for a trace in the model checkable representation of a test formula.
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
	protected Element createMCTrace(final Element trace, final String commonExitSync) {
		final Element parentNode1 = (Element) trace.getParentNode();
		Element parentNode2 = null;
		if (!parentNode1.getNodeName().equals(XMLTags.TESTFORmTAG)) {
			parentNode2 = (Element) parentNode1.getParentNode();
		}
		final boolean traceIsFirstChild = isFirstChild(trace);
		boolean parentNode1IsFirstChild;
		if (parentNode2 != null) {
			parentNode1IsFirstChild = isFirstChild(parentNode1);
		} else {
			parentNode1IsFirstChild = true;
		}
		String syncEvent1 = null;
		String syncEvent2 = null;

		if (parentNode1.getAttribute(XMLTags.OPERATOR_TAG).startsWith(XMLTags.SYNC_PREFIX)) {
			syncEvent1 = parentNode1.getAttribute(XMLTags.OPERATOR_TAG);
		}
		if (parentNode2 != null) {
			if (parentNode2.getAttribute(XMLTags.OPERATOR_TAG).startsWith(XMLTags.SYNC_PREFIX)) {
				syncEvent2 = parentNode2.getAttribute(XMLTags.OPERATOR_TAG);
			}
		}

		if (syncEvent1 == null) {
			logger.debug("SyncEvent1==null");
			if (isTrueNode(trace)) {
				return null;
			}
			return getMCTraceNode((Element) trace.cloneNode(true), null, commonExitSync);
		}
		if (traceIsFirstChild) {
			if (syncEvent2 == null || parentNode1IsFirstChild) {
				logger.debug("traceIsFirstChild && " + "(syncEvent2==NULL || parentNode1IsFirstChild");
				if (isTrueNode(trace)) {
					return null;
				}
				return getMCTraceNode((Element) trace.cloneNode(true), null, syncEvent1);
			}
			logger.debug("traceIsFirstChild && " + "(syncEvent2!=NULL && !parentNode1IsFirstChild");
			if (isAlreadyHandled(syncEvent2, syncEvent1) && isTrueNode(trace)) {
				return null;
			}
			return getMCTraceNode((Element) trace.cloneNode(true), syncEvent2, syncEvent1);
		}
		if (syncEvent2 == null || !parentNode1IsFirstChild) {
			logger.debug("!traceIsFirstChild && " + "(syncEvent2==NULL || parentNode1IsFirstChild");
			if (isTrueNode(trace)) {
				return null;
			}
			return getMCTraceNode((Element) trace.cloneNode(true), syncEvent1, commonExitSync);
		}
		logger.debug("!traceIsFirstChild && " + "(syncEvent2!=NULL && parentNode1IsFirstChild");
		if (isAlreadyHandled(syncEvent1, syncEvent2) && isTrueNode(trace)) {
			return null;
		}
		return getMCTraceNode((Element) trace.cloneNode(true), syncEvent1, syncEvent2);
	}

	/**
	 * Delivers a fresh sync event
	 */
	private String getFreshSyncEvent() {
		final String result = XMLTags.SYNC_PREFIX + syncEventCounter;
		syncEventCounter++;
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
	protected Element getMCTraceNode(final Element traceNode, final String entrySync, final String exitSync) {
		final Element mcTraceNode = document.createElement(XMLTags.MCTRACE_TAG);

		if (entrySync != null) {
			if (entrySync.equals("")) {
				throw new RuntimeException("Existing entry sync events " + "are not allowed to be empty");
			}
			mcTraceNode.setAttribute(XMLTags.ENTRYSYNC_TAG, entrySync);
		}

		if (exitSync.equals("")) {
			throw new RuntimeException("Exit sync events are not allowed to be empty");
		}
		mcTraceNode.setAttribute(XMLTags.EXITSYNC_TAG, exitSync);
		mcTraceNode.appendChild(traceNode);

		handledIntervalsList.add(entrySync + exitSync);
		return mcTraceNode;
	}

	private boolean isTrueNode(final Element traceNode) {
		return trueNodeList.contains(traceNode);
	}

	private boolean isAlreadyHandled(final String sync1, final String sync2) {
		return handledIntervalsList.contains(sync1 + sync2);
	}

	private boolean isFirstChild(final Node node) {
		final Element parent = (Element) node.getParentNode();
		final Element[] operands = getFormulaOperands(parent);
		return node == operands[0];
	}

	/**
	 * Implements the inherited methods with correct XML-Tags
	 */
	@Override
	protected Element getNewTreeElement() {
		return document.createElement(XMLTags.TFTREE_TAG);
	}

	@Override
	protected boolean isTreeElement(final Node node) {
		return node.getNodeName().equals(XMLTags.TFTREE_TAG);
	}

	@Override
	protected boolean isBasicElement(final Node node) {
		return node.getNodeName().equals(XMLTags.TRACE_TAG);
	}

	@Override
	protected boolean isFormulaElement(final Node node) {
		return node.getNodeName().equals(XMLTags.TESTFORmTAG);
	}

	@Override
	protected boolean isCorrectOperator(final String operator) {
		return operator.equals(XMLTags.OR_CONST) || operator.equals(XMLTags.AND_CONST)
		        || operator.equals(XMLTags.CHOP_CONST) || operator.startsWith(XMLTags.SYNC_PREFIX);
	}
}
