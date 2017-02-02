/* $Id: FormulaJ2XMLConverter.java 408 2009-07-17 09:54:06Z jfaber $
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
import java.util.List;
import java.util.Vector;

import org.apache.xerces.dom.DocumentImpl;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Decision;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.ZDecision;
import net.sourceforge.czt.parser.util.ParseException;

/**
 * The class <code>FormulaJ2XMLConverter</code> offers functionality to convert a <code>CDD</code> object into a
 * <code>FormulaTree</code> as specified in <code>pea.modelchecking.schemas.BasicTypes.xsd</code>.
 *
 * @author Roland Meyer
 *
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.CDD
 * @see pea.modelchecking.schemas.BasicTypes.xsd
 */
public class FormulaJ2XMLConverter {

	private static final String DEFAULT_LOGGER = "FormulaJ2XMLConverter";

	ILogger mLogger = null;

	Document mDocument = null;

	protected List<String> mRangeExpressionVariables = null;

	protected List<String> mEvents = null;

	private final Vector<String> mDisjuncts = new Vector<>();

	private int mDnfCount = 1;

	/**
	 * Initialises the FormulaJ2XMLConverter object. Takes as parameter a string that defines the loggername for the
	 * built in log4j logger. If the string is empty, the default name <code>FormulaJ2XMLConverter</code> is used. An
	 * application using a FormulaJ2XMLConverter object has to make sure that the logger is initialised via
	 * <code>PropertyConfigurator.configure()</code>.
	 * 
	 * @param loggerName
	 * @see ILogger
	 * @see PropertyConfigurator
	 */
	public FormulaJ2XMLConverter(final String loggerName) {
		if (loggerName.equals("")) {
			mLogger = ILogger.getLogger(FormulaJ2XMLConverter.DEFAULT_LOGGER);
		} else {
			mLogger = ILogger.getLogger(loggerName);
		}
	}

	/**
	 * Initialises the FormulaJ2XMLConverter object with the default logger.
	 */
	public FormulaJ2XMLConverter() {
		this("");
	}

	/**
	 * Creates a <code>FormulaTree</code> element for the given CDD by a recursive algorithm using the
	 * <code>createCDDFormula</code> method. The resulting element needs to be importet into the document of the calling
	 * application. All variables that occur in RangeDecisions inside <code>formulaCDD</code> are stored in the passed
	 * ArrayList <code>rangeExpressionVariables</code>. All events in EventDecisions inside <code>formulaCDD</code> are
	 * stored in the passed ArrayList <code>events</code>
	 * 
	 * @param formulaCDD
	 *            The <code>CDD</code> to convert
	 * @param rangeExpressionVariables
	 *            The ArrayList to store variables in RangeDecisions
	 * @param events
	 *            The ArrayList to store event names in EventDecisions.
	 * @return The <code>FormulaTree</code> element. This element is not in the document of the calling application and
	 *         needs to be importet.
	 * 
	 * @see org.w3c.dom.Element
	 * @see org.w3c.dom.Document
	 * @see org.w3c.dom.Document.importNode
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.CDD
	 * @see pea.modelchecking.schemas.BasicTypes.xsd
	 */
	public Element convert(final CDD formulaCDD, final List<String> rangeExpressionVariables,
			final List<String> events) {
		mDocument = new DocumentImpl();

		this.mRangeExpressionVariables = rangeExpressionVariables;
		this.mEvents = events;

		mLogger.debug("Trying to build formula node");
		final Element result = createCDDFormula(formulaCDD);
		mLogger.debug("Building formula node successful");

		return result;
	}

	/**
	 * Returns the <code>org.w3c.dom.Element</code> representation of CDD <code>formulaCDD</code>. Recursively calls
	 * this method for children of <code>formulaCDD</code>. If a CDD has the same operator as it's child, the elements
	 * representing the grandchildren are directly appended to the element representing the CDD. Furthermore
	 * <code>formulaTree</code> children are listed behind <code>RangeExpression</code>, <code>EventExpression</code>,
	 * and <code>BooleanExpression</code> children to improve readability of the xml output.
	 * 
	 * @param formulaCDD
	 *            The CDD to convert
	 * @return The <code>org.w3c.dom.Element</code> representation of the CDD
	 * 
	 * @see org.w3c.dom.Element
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.CDD
	 * @see pea.modelchecking.schemas.BasicTypes.xsd
	 */
	private Element createCDDFormula(final CDD formulaCDD) {
		if (formulaCDD == CDD.TRUE) {
			return createBooleanExpressionNode(XMLTags.TRUE_CONST);
		}
		if (formulaCDD == CDD.FALSE) {
			return createBooleanExpressionNode(XMLTags.FALSE_CONST);
		}

		final CDD[] children = formulaCDD.getChilds();
		final List<Node> simpleChildNodes = new ArrayList<>();
		final List<Node> complexChildNodes = new ArrayList<>();
		for (int i = 0; i < children.length; i++) {
			if (children[i] == CDD.FALSE) {
				continue;
			}
			if (formulaCDD.childDominates(i)) {
				final Element actChildNode = createCDDFormula(children[i]);
				if (actChildNode.getNodeName().equals(XMLTags.FORMULATREE_TAG)) {

					// Simplify nested disjunctions
					if (actChildNode.getAttribute(XMLTags.OPERATOR_TAG).equals(XMLTags.OR_CONST)) {
						final NodeList grandChildren = actChildNode.getChildNodes();
						final int grandChildCount = grandChildren.getLength();
						for (int j = 0; j < grandChildCount; j++) {
							if (grandChildren.item(j).getNodeName().equals(XMLTags.FORMULATREE_TAG)) {
								complexChildNodes.add(grandChildren.item(j));
							} else {
								simpleChildNodes.add(grandChildren.item(j));
							}
						}

					} else {
						complexChildNodes.add(actChildNode);
					}
				} else {
					simpleChildNodes.add(actChildNode);
				}
			} else {
				final Element decisionNode = createDecisionNode(formulaCDD.getDecision(), i);
				if (children[i] != CDD.TRUE) {
					final Element actChildNode = createCDDFormula(children[i]);
					final Element formulaTreeAND = createDecisionAndChildTree(decisionNode, actChildNode);
					complexChildNodes.add(formulaTreeAND);
				} else {
					simpleChildNodes.add(decisionNode);
				}
			}
		}

		if (simpleChildNodes.isEmpty() && complexChildNodes.isEmpty()) {
			throw new RuntimeException("The cdd " + formulaCDD + " has no children");
		}

		if (simpleChildNodes.size() == 1 && complexChildNodes.isEmpty()) {
			return (Element) simpleChildNodes.get(0);
		}

		if (complexChildNodes.size() == 1 && simpleChildNodes.isEmpty()) {
			return (Element) complexChildNodes.get(0);
		}

		final Element actFormulaTree = mDocument.createElement(XMLTags.FORMULATREE_TAG);
		actFormulaTree.setAttribute(XMLTags.OPERATOR_TAG, XMLTags.OR_CONST);

		final Iterator<Node> simpleChildNodeIterator = simpleChildNodes.iterator();
		while (simpleChildNodeIterator.hasNext()) {
			final Element actChildNode = (Element) simpleChildNodeIterator.next();
			actFormulaTree.appendChild(actChildNode);
		}
		final Iterator<Node> complexChildNodeIterator = complexChildNodes.iterator();
		while (complexChildNodeIterator.hasNext()) {
			final Element actChildNode = (Element) complexChildNodeIterator.next();
			actFormulaTree.appendChild(actChildNode);
		}

		return actFormulaTree;
	}

	/**
	 * Connects a decision node and its child node via a formula tree element. If the child node also has an
	 * <code>AND</code> -operator, the grandchildren are directly appended to the formula tree. Furthermore children are
	 * sorted, RangeExpressions, BooleanExpressions, and EventExpressions are listed before formulaTrees for improved
	 * readability of the XML-output.
	 * 
	 * @param decisionNode
	 *            The decision node to be appended to the formula tree
	 * @param childNode
	 *            The child of the decision node.
	 * @return The formula tree
	 * 
	 * @see pea.modelchecking.schemas.BasicTypes.xsd
	 */
	private Element createDecisionAndChildTree(final Element decisionNode, final Element childNode) {
		final Element formulaTreeAND = mDocument.createElement(XMLTags.FORMULATREE_TAG);
		formulaTreeAND.setAttribute(XMLTags.OPERATOR_TAG, XMLTags.AND_CONST);

		formulaTreeAND.appendChild(decisionNode);

		// Simplify nested conjunctions
		if (childNode.getAttribute(XMLTags.OPERATOR_TAG).equals(XMLTags.AND_CONST)) {
			final NodeList grandChildren = childNode.getChildNodes();
			final List<Element> left = new ArrayList<>();
			for (int i = grandChildren.getLength() - 1; i >= 0; i--) {
				final Element actGrandChild = (Element) grandChildren.item(i);
				if (actGrandChild.getNodeName().equals(XMLTags.FORMULATREE_TAG)) {
					left.add(actGrandChild);
				} else {
					formulaTreeAND.appendChild(actGrandChild);
				}
			}

			// Operands that are trees theirselves are appended for improved
			// readability of the XML-file.
			for (final Element actGrandChild : left) {
				formulaTreeAND.appendChild(actGrandChild);
			}

		} else {
			formulaTreeAND.appendChild(childNode);
		}

		return formulaTreeAND;
	}

	/**
	 * Creates the <code>org.w3c.dom.Element</code> representation of a <code>pea.Decision</code>. If the index
	 * <code>i</code> is not 0 and <code>decision</code> instance of <code>BooleanDecision</code> or
	 * <code>EventDecision</code>, the resulting <code>org.w3c.dom.Element</code> is negated using a formula tree with
	 * operator <code>NOT</code>.
	 * <p>
	 * Throws a <code>RuntimeException</code> if the decision is not an instance of <code>pea.BooleanDecision</code>,
	 * <code>pea.EventDecision</code>, or <code>pea.RangeDecision</code>.
	 * 
	 * @param decision
	 *            The decision to be transformed
	 * @param i
	 *            The indication whether the representation of the decision needs to be negated( <code>i!=0</code>).
	 * @return The <code>org.w3c.dom.Element</code> representation of the decision
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.Decision
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision
	 * @see pea.modelchecking.schemas.BasicTypes.xsd
	 */
	private Element createDecisionNode(final Decision decision, final int i) {
		if (!(decision instanceof BooleanDecision) && !(decision instanceof EventDecision)
				&& !(decision instanceof RangeDecision) && !(decision instanceof ZDecision)) {
			throw new RuntimeException("Decision has to be instance of " + "\"BooleanDecision\", "
					+ "\"EventDecision\", or " + "\"RangeDecision\"");
		}

		if (decision instanceof RangeDecision) {
			final Element rangeDecisionNode = createRangeExpressionNode((RangeDecision) decision, i);
			return rangeDecisionNode;
		}

		Element expressionNode = null;
		if (decision instanceof BooleanDecision) {
			final String variable = ((BooleanDecision) decision).getVar();
			expressionNode = createBooleanExpressionNode(variable);
		} else if (decision instanceof EventDecision) {
			final String event = ((EventDecision) decision).getEvent();
			expressionNode = createEventExpressionNode(event);
		} else if (decision instanceof ZDecision) {
			final Element zNode = mDocument.createElement(XMLTags.Z_TAG);
			try {
				zNode.setTextContent(((ZDecision) decision).getZML());
			} catch (final ParseException e) {
				zNode.setTextContent(e.toString());
			} catch (final InstantiationException e) {
				zNode.setTextContent(e.toString());
			}
			expressionNode = zNode;
		}

		if (i == 0) {
			return expressionNode;
		}
		final Element notFormulaNode = mDocument.createElement(XMLTags.FORMULATREE_TAG);
		notFormulaNode.setAttribute(XMLTags.OPERATOR_TAG, XMLTags.NOT_CONST);
		notFormulaNode.appendChild(expressionNode);
		return notFormulaNode;
	}

	/**
	 * Returns a <code>BooleanExpression</code> element representing the expression <code>expression</code>.
	 * <p>
	 * Throws a <code>RuntimeException</code> if the expression is empty, meaning <code>expression.equals("")</code>.
	 * 
	 * @param expression
	 *            The expression a <code>BooleanExpression</code> as <code>org.w3c.dom.Element</code> needs to be
	 *            constructed for.
	 * @return The constructed <code>BooleanExpression</code> element.
	 * 
	 * @see pea.modelchecking.schemas.BasicTypes.xsd
	 */
	private Element createBooleanExpressionNode(final String expression) {
		if (expression.equals("")) {
			throw new RuntimeException("Boolean expressions with empty content are not allowed");
		}

		final Element expressionNode = mDocument.createElement(XMLTags.BOOLEANEXPRESSION_TAG);
		expressionNode.setAttribute(XMLTags.EXPRESSION_TAG, expression.replace("<", "&lt;").replace(">", "&gt;"));
		return expressionNode;
	}

	/**
	 * Returns a <code>RangeExpression</code> element representing the RangeDecision <code>decision</code>. As negations
	 * are directly resolved in <code>RangeDecisions</code> by changing the operators ( <, <=, >, >=), the index
	 * indicates which operator to use.
	 * <p>
	 * Throws a <code>RuntimeException</code> if <code>decision.getVar</code> is empty, meaning
	 * <code>decision.getVar().equals("")</code>.
	 * 
	 * @param decision
	 *            The decision a <code>RangeExpression</code> as <code>org.w3c.dom.Element</code> needs to be
	 *            constructed for.
	 * @param i
	 *            Indicating whether <code>decision</code> is negated ( <code>i!=0</code>)
	 * @return The constructed <code>RangeExpression</code> element.
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision
	 * @see pea.modelchecking.schemas.BasicTypes.xsd
	 */
	private Element createRangeExpressionNode(final RangeDecision decision, final int i) {
		final Element rangeExpressionNode = mDocument.createElement(XMLTags.RANGEEXPRESSION_TAG);

		final String variable = decision.getVar();
		if (variable.equals("")) {
			throw new RuntimeException("Variables are not allowed to be empty");
		}
		rangeExpressionNode.setAttribute(XMLTags.VARIABLE_TAG, variable);

		if (!mRangeExpressionVariables.contains(variable)) {
			mRangeExpressionVariables.add(variable);
		}

		final int[] limits = decision.getLimits();
		if (i == 0) {
			if ((limits[0] & 1) == 0) {
				rangeExpressionNode.setAttribute(XMLTags.OPERATOR_TAG, XMLTags.LESS_CONST);
			} else {
				rangeExpressionNode.setAttribute(XMLTags.OPERATOR_TAG, XMLTags.LESSEQUAL_CONST);
			}

			rangeExpressionNode.setAttribute(XMLTags.BOUND_TAG, Integer.toString(limits[0] / 2));
			return rangeExpressionNode;
		}
		if (i == limits.length) {
			if ((limits[limits.length - 1] & 1) == 1) {
				rangeExpressionNode.setAttribute(XMLTags.OPERATOR_TAG, XMLTags.GREATER_CONST);
			} else {
				rangeExpressionNode.setAttribute(XMLTags.OPERATOR_TAG, XMLTags.GREATEREQUAL_CONST);
			}
			rangeExpressionNode.setAttribute(XMLTags.BOUND_TAG, Integer.toString(limits[limits.length - 1] / 2));
			return rangeExpressionNode;
		}
		if (limits[i - 1] / 2 == limits[i] / 2) {
			rangeExpressionNode.setAttribute(XMLTags.OPERATOR_TAG, XMLTags.EQUAL_CONST);
			rangeExpressionNode.setAttribute(XMLTags.BOUND_TAG, Integer.toString(limits[i] / 2));
			return rangeExpressionNode;
		}

		final Element formulaTreeNode = mDocument.createElement(XMLTags.FORMULATREE_TAG);
		formulaTreeNode.setAttribute(XMLTags.OPERATOR_TAG, XMLTags.AND_CONST);
		if ((limits[i - 1] & 1) == 1) {
			rangeExpressionNode.setAttribute(XMLTags.OPERATOR_TAG, XMLTags.GREATER_CONST);
		} else {
			rangeExpressionNode.setAttribute(XMLTags.OPERATOR_TAG, XMLTags.GREATEREQUAL_CONST);
		}
		rangeExpressionNode.setAttribute(XMLTags.BOUND_TAG, Integer.toString(limits[i - 1] / 2));

		final Element rangeExpressionNode2 = mDocument.createElement(XMLTags.RANGEEXPRESSION_TAG);
		rangeExpressionNode2.setAttribute(XMLTags.VARIABLE_TAG, variable);

		if ((limits[i] & 1) == 0) {
			rangeExpressionNode2.setAttribute(XMLTags.OPERATOR_TAG, XMLTags.LESS_CONST);
		} else {
			rangeExpressionNode2.setAttribute(XMLTags.OPERATOR_TAG, XMLTags.LESSEQUAL_CONST);
		}
		rangeExpressionNode2.setAttribute(XMLTags.BOUND_TAG, Integer.toString(limits[i] / 2));

		formulaTreeNode.appendChild(rangeExpressionNode);
		formulaTreeNode.appendChild(rangeExpressionNode2);

		return formulaTreeNode;
	}

	/**
	 * Returns an <code>EventExpression</code> element representing the event <code>event</code>.
	 * <p>
	 * Throws a <code>RuntimeException</code> if the event is empty, meaning <code>event.equals("")</code>.
	 * 
	 * @param event
	 *            The event an <code>EventExpression</code> as <code>org.w3c.dom.Element</code> needs to be constructed
	 *            for.
	 * @return The constructed <code>EventExpression</code> element.
	 * 
	 * @see pea.modelchecking.schemas.BasicTypes.xsd
	 */
	private Element createEventExpressionNode(final String event) {
		if (event.equals("")) {
			throw new RuntimeException("Events are not allowed to be empty");
		}

		if (!mEvents.contains(event)) {
			mEvents.add(event);
		}

		final Element eventNode = mDocument.createElement(XMLTags.EVENTEXPRESSION_TAG);
		eventNode.setAttribute(XMLTags.NAME_Tag, event);
		return eventNode;
	}

	public String[] getDisjuncts(final CDD cdd, final List<String> rangeExpressionVariables, final List<String> events,
			final int numberOfDNFs) {
		mDisjuncts.clear();

		this.mRangeExpressionVariables = rangeExpressionVariables;
		this.mEvents = events;

		/*
		 * System.out.println("Computing DNF " + dnfCount + ((numberOfDNFs == 0) ? "" : Integer.toStringnumberOfDNFs));
		 */
		mDnfCount++;
		cddToDNF(new StringBuilder(), cdd);

		final int disjunctCount = mDisjuncts.size();
		final String[] strings = new String[disjunctCount];
		for (int i = 0; i < disjunctCount; i++) {
			strings[i] = mDisjuncts.elementAt(i);

		}

		return strings;
	}

	public String[] getDisjuncts(final CDD cdd, final List<String> rangeExpressionVariables,
			final List<String> events) {
		return getDisjuncts(cdd, rangeExpressionVariables, events, 0);
	}

	private void cddToDNF(final StringBuilder buf, final CDD cdd) {
		if (cdd == CDD.TRUE) {
			mDisjuncts.add(buf.toString());
			return;
		} else if (cdd == CDD.FALSE) {
			return;
		}
		for (int i = 0; i < cdd.getChilds().length; i++) {
			final StringBuilder newBuf = new StringBuilder(buf);
			// newBuf.append(buf.toString());
			// TODO: Hier ist noch ein Bug. Die Unds innerhalb eines Disjunkts
			// werden noch nicht geschrieben.
			appendDecisionToBuffer(newBuf, cdd.getDecision(), i);

			cddToDNF(newBuf, cdd.getChilds()[i]);
		}
	}

	private void appendDecisionToBuffer(final StringBuilder buf, final Decision dec, final int i) {
		if (dec instanceof RangeDecision) {
			final String variable = ((RangeDecision) dec).getVar();
			buf.append("  <rangeExpression variable=\"" + variable + "\" ");

			if (!mRangeExpressionVariables.contains(variable)) {
				mRangeExpressionVariables.add(variable);
			}

			final int[] limits = ((RangeDecision) dec).getLimits();
			if (i == 0) {
				if ((limits[0] & 1) == 0) {
					buf.append("operator = \"less\" ");
				} else {
					buf.append("operator = \"lessequal\" ");
				}
				buf.append("bound = \"" + limits[0] / 2 + "\"/>\n");
				return;
			}
			if (i == limits.length) {
				if ((limits[limits.length - 1] & 1) == 1) {
					buf.append("operator = \"greater\" ");
				} else {

					buf.append("operator = \"greaterequal\" ");
				}
				buf.append("bound = \"" + limits[limits.length - 1] / 2 + "\"/>\n");
				return;
			}
			if (limits[i - 1] / 2 == limits[i] / 2) {
				buf.append("operator = \"greater\" ");
				buf.append("bound = \"" + limits[i] / 2 + "\"/>");
				return;
			}
			if ((limits[i - 1] & 1) == 1) {
				buf.append("operator = \"greater\" ");
			} else {
				buf.append("operator = \"greaterequal\" ");
			}
			buf.append("bound = \"" + limits[i - 1] / 2 + "\"/>\n");

			buf.append("  <rangeExpression variable=\"" + variable + "\" ");

			if ((limits[i] & 1) == 0) {
				buf.append("operator = \"less\" ");
			} else {
				buf.append("operator = \"lessequal\" ");
			}
			buf.append("bound = \"" + limits[i] / 2 + "\"/>\n");
			return;
		}
		if (i == 0) {
			if (dec instanceof BooleanDecision) {
				buf.append("  <booleanExpression expression=\""
						+ ((BooleanDecision) dec).getVar().replace("<", "&lt;").replace(">", "&gt;") + "\"/>\n");
			} else if (dec instanceof EventDecision) {
				final String event = ((EventDecision) dec).getEvent();
				if (!mEvents.contains(event)) {
					mEvents.add(event);
				}
				buf.append("  <eventExpression name=\"" + event + "\"/>\n");
			} else if (dec instanceof ZDecision) {
				try {
					buf.append(((ZDecision) dec).getZML());
				} catch (final ParseException e) {
					e.printStackTrace();
				} catch (final InstantiationException e) {
					e.printStackTrace();
				}
			}
		} else {
			if (dec instanceof BooleanDecision) {
				buf.append("  <formulaTree operator = \"NOT\">\n");
				buf.append("    <booleanExpression expression=\""
						+ ((BooleanDecision) dec).getVar().replace("<", "&lt;").replace(">", "&gt;") + "\"/>\n");
				buf.append("  </formulaTree>\n");
			} else if (dec instanceof EventDecision) {
				final String event = ((EventDecision) dec).getEvent();
				if (!mEvents.contains(event)) {
					mEvents.add(event);
				}
				buf.append("  <formulaTree operator = \"NOT\">\n");
				buf.append("    <eventExpression name=\"" + event + "\"/>\n");
				buf.append("  </formulaTree>\n");
			} else if (dec instanceof ZDecision) {
				try {
					buf.append(((ZDecision) dec).negate().getZML());
				} catch (final ParseException p) {
					// this exception occurs if the negation is not computed
					// correctly
					p.printStackTrace();
				} catch (final InstantiationException p) {
					p.printStackTrace();
				}
			}
		}
	}

	public String convertFast(final CDD formulaCDD, final List<String> rangeExpressionVariables,
			final List<String> events) {
		final XMLWriter writer = new XMLWriter();
		final String result = writer.writeXMLDocumentToString(convert(formulaCDD, rangeExpressionVariables, events));

		return result.substring(1, result.length()) + "\n";
	}

	/**
	 * Generates an XML string from the given CDD. In opposite to previous implementations, this is done along the lines
	 * of CDD.toString. That is in particular, the resulting XML-formula is not in DNF due to effenciency reasons.
	 * 
	 * @param cdd
	 *            The CDD for that the XML representation is to be calculated
	 * @return A string containing the XML representation.
	 */
	public StringBuilder cddToXML(final CDD cdd) {
		// logger.debug("Processing CDD " + cdd);
		final StringBuilder sb = new StringBuilder();
		boolean ordelim = false;
		int clauses = 0;
		if (cdd == CDD.TRUE) {
			return new StringBuilder("<booleanExpression expression=\"true\"/>");
		}
		if (cdd == CDD.FALSE) {
			return new StringBuilder("<booleanExpression expression=\"false\"/>");
		}

		final CDD[] childs = cdd.getChilds();
		for (int j = 0; j < childs.length; j++) {
			if (ordelim && childs[j] != CDD.FALSE) {
				sb.append("<formulaTree operator = \"OR\">\n");
			} else if (childs[j] != CDD.FALSE) {
				ordelim = true;
			}
		}

		ordelim = false;
		for (int i = 0; i < childs.length; i++) {
			if (childs[i] == CDD.FALSE) {
				continue;
			}

			if (cdd.childDominates(i)) {
				sb.append(cddToXML(childs[i]));
			} else {
				if (childs[i] != CDD.TRUE) {
					sb.append("<formulaTree operator = \"AND\">\n");
					appendDecisionToBuffer(sb, cdd.getDecision(), i);
					sb.append(cddToXML(childs[i]));
					sb.append("</formulaTree>\n");
				} else {
					appendDecisionToBuffer(sb, cdd.getDecision(), i);
				}

			}

			if (ordelim) {
				sb.append("</formulaTree>\n");
			} else {
				ordelim = true;
			}

			clauses++;
		}

		return sb;
	}

	/**
	 * @param guard
	 * @param clocks
	 * @param events2
	 * @return
	 */
	public String formulaToXML(final CDD guard, final List<String> rangeExpressionVariables,
			final List<String> events) {
		this.mRangeExpressionVariables = rangeExpressionVariables;
		this.mEvents = events;
		return cddToXML(guard).toString();
	}

}
