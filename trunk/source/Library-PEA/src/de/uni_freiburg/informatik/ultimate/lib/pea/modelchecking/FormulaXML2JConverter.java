/* $Id: FormulaXML2JConverter.java 406 2009-07-09 10:44:35Z jfaber $
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

import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.RelationDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.RelationDecision.Operator;

/**
 * The class <code>FormulaXML2JConverter</code> offers functionality to convert a <code>FormulaTree</code> as specified
 * in <code>pea.modelchecking.schemas.BasicTypes.xsd</code> into a <code>CDD</code> object.
 *
 * @author Roland Meyer
 *
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.CDD
 * @see pea.modelchecking.schemas.BasicTypes.xsd
 */
public class FormulaXML2JConverter {

	private static final String DEFAULT_LOGGER = "FormulaXML2JConverter";

	private ILogger logger = null;

	// Flag to choose whether booleanDecision or ZDecision should be generated from a formula
	protected boolean useZDecision = false;

	/**
	 * Initialises the FormulaXML2JConverter object. Takes as parameter a string that defines the loggername for the
	 * built in log4j logger. If the string is empty, the default name <code>FormulaXML2JConverter</code> is used. An
	 * application using a FormulaXML2JConverter object has to make sure that the logger is initialised via
	 * <code>PropertyConfigurator.configure()</code>.
	 * 
	 * @param loggerName
	 * @see ILogger
	 * @see PropertyConfigurator
	 */
	public FormulaXML2JConverter(final String loggerName, final boolean useZDecision) {
		if (loggerName.equals("")) {
			logger = ILogger.getLogger(FormulaXML2JConverter.DEFAULT_LOGGER);
		} else {
			logger = ILogger.getLogger(loggerName);
		}
		this.useZDecision = useZDecision;
	}

	/**
	 * Initialises the FormulaXML2JConverter object with the default logger.
	 */
	public FormulaXML2JConverter(final boolean useZDecision) {
		this("", useZDecision);
	}

	/**
	 * Creates a <code>CDD</code> object for the given <code>formulaNode</code> element by a recursive algorithm using
	 * the <code>createFormulaCDD</code> method.
	 * 
	 * @param formulaNode
	 *            The <code>org.w3c.dom.Element</code> to convert
	 * @return The <code>CDD</code> representation of <code>formulaNode</code>.
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.CDD
	 * @see pea.modelchecking.schemas.BasicTypes.xsd
	 */
	public CDD convert(final Element formulaNode) {
		final Element[] formulaContent = getFormulaOperands(formulaNode);
		if (formulaContent.length != 1) {
			throw new RuntimeException("Formulae with child count != 1 are not allowed");
		}

		logger.info("Trying to build CDD");
		final CDD result = createFormulaCDD(formulaContent[0]);
		logger.info("Building CDD successful");

		return result;
	}

	/**
	 * Returns the <code>CDD</code> representation of <code>formula</code>. Recursively calls this method for children
	 * of <code>formula</code>.
	 * 
	 * @param formula
	 *            The <code>org.w3c.dom.Element</code> to convert
	 * @return The <code>CDD</code> representation of <code>formula</code>
	 * @throws <code>RuntimeException</code>
	 *             if
	 *             <ul>
	 *             <li>A formulaTree with operator <code>pea.modelchecking.XMLTags.NOT_CONST</code> has not exactly one
	 *             operand
	 *             <li>A formulaTree with operator <code>pea.modelchecking.XMLTags.AND_CONST</code> or
	 *             <code>pea.modelchecking.XMLTags.OR_CONST</code> has less than two operands
	 *             <li>A formulaTree has an operator different from <code>pea.modelchecking.XMLTags.NOT_CONST</code>,
	 *             <code>pea.modelchecking.XMLTags.AND_CONST</code>, <code>pea.modelchecking.XMLTags.OR_CONST</code>.
	 *             <li><code>formula</code> has a tag name different from
	 *             <code>pea.modelchecking.XMLTags.BOOLEANEXPRESSION_TAG</code>,
	 *             <code>pea.modelchecking.XMLTags.RANGEEXPRESSION_TAG</code>,
	 *             <code>pea.modelchecking.XMLTags.EVENTEXPRESSION_TAG</code>,
	 *             <code>pea.modelchecking.XMLTags.FORMULATREE_TAG</code>.
	 *             </ul>
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.CDD
	 * @see pea.modelchecking.schemas.BasicTypes.xsd
	 */
	private CDD createFormulaCDD(final Element formula) {
		final String formulaName = formula.getNodeName();
		if (formulaName.equals(XMLTags.BOOLEANEXPRESSION_TAG)) {
			return /*
			        * useZDecision ? this.createZDecision(formula) :
			        */ createBooleanDecision(formula);
		} else if (formulaName.equals(XMLTags.RANGEEXPRESSION_TAG)) {
			return createRangeDecision(formula);
		} else if (formulaName.equals(XMLTags.EVENTEXPRESSION_TAG)) {
			return createEventDecision(formula);
		} else if (formulaName.equals(XMLTags.FORMULATREE_TAG)) {
			final Element[] children = getFormulaOperands(formula);
			final String operator = formula.getAttribute(XMLTags.OPERATOR_TAG);
			if (operator.equals(XMLTags.NOT_CONST)) {
				if (children.length != 1) {
					throw new RuntimeException("Child count != 1 is not allowed" + " for formula trees with \""
					        + XMLTags.NOT_CONST + "\"-operator ");
				}
				final CDD negatedFormula = createFormulaCDD(children[0]).negate();
				return negatedFormula;
			} else if (operator.equals(XMLTags.OR_CONST)) {
				if (children.length < 2) {
					throw new RuntimeException(
					        "\"" + XMLTags.OR_CONST + "\" formulae with < 2 operands are not allowed");
				}
				CDD orFormula = CDD.FALSE;
				for (int i = 0; i < children.length; i++) {
					orFormula = orFormula.or(createFormulaCDD(children[i]));
				}
				return orFormula;
			} else if (operator.equals(XMLTags.AND_CONST)) {
				if (children.length < 2) {
					throw new RuntimeException(
					        "\"" + XMLTags.AND_CONST + "\" formulae with < 2 operands are not allowed");
				}
				CDD andFormula = CDD.TRUE;
				for (int i = 0; i < children.length; i++) {
					andFormula = andFormula.and(createFormulaCDD(children[i]));
				}
				return andFormula;
			}
			throw new RuntimeException("Formula tree operator has to be \"" + XMLTags.NOT_CONST + "\", \""
			        + XMLTags.AND_CONST + "\", or \"" + XMLTags.OR_CONST + "\"");
		}
		throw new RuntimeException("Formula has to be \"" + XMLTags.BOOLEANEXPRESSION_TAG + "\", \""
		        + XMLTags.EVENTEXPRESSION_TAG + "\", or \"" + XMLTags.RANGEEXPRESSION_TAG + "\"");
	}

	/**
	 * Returns the children with tag name <code>pea.modelchecking.XMLTags.RANGEEXPRESSION_TAG</code>,
	 * <code>pea.modelchecking.XMLTags.BOOLEANEXPRESSION_TAG</code>,
	 * <code>pea.modelchecking.XMLTags.EVENTEXPRESSION_TAG</code>,
	 * <code>pea.modelchecking.XMLTags.FORMULATREE_TAG</code> of a formula.
	 * 
	 * @param formula
	 *            FormulaTree the operands need to be found for
	 * @return The array of operands as <code>org.w3c.dom.Element</code> objects
	 * @throws <code>RuntimeException</code>
	 *             if the number of operands is 0.
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.XMLTags
	 * @see pea.modelchecking.schemas.BasicTypes.xsd
	 */
	private Element[] getFormulaOperands(final Element formula) {
		final ArrayList<Element> result = new ArrayList<Element>();
		final NodeList children = formula.getChildNodes();
		final int childrenCount = children.getLength();
		for (int i = 0; i < childrenCount; i++) {
			final Node actChild = children.item(i);
			final String actChildName = actChild.getNodeName();
			if (actChildName.equals(XMLTags.RANGEEXPRESSION_TAG) || actChildName.equals(XMLTags.BOOLEANEXPRESSION_TAG)
			        || actChildName.equals(XMLTags.EVENTEXPRESSION_TAG)
			        || actChildName.equals(XMLTags.FORMULATREE_TAG)) {
				result.add((Element) actChild);
			}
		}

		final int resultSize = result.size();
		if (resultSize == 0) {
			throw new RuntimeException("A formula with 0 operands is not allowed.");
		}

		return result.toArray(new Element[resultSize]);
	}

	/**
	 * Converts the string <code>operator</code> from <code>pea.modelchecking.XMLTags</code> constants
	 * <code>XMLTags.GREATEREQUAL_CONST</code>, <code>XMLTags.GREATER_CONST</code>,<code>XMLTags.LESS_CONST</code>,
	 * <code>XMLTags.LESSEQUAL_CONST</code>,<code>XMLTags.EQUAL_CONST</code>, <code>XMLTags.NOTEQUAL_CONST</code> to the
	 * according int constant in <code>pea.RangeDecision</code>.
	 * 
	 * @param operator
	 *            String of operator to be translated
	 * @return The <code>pea.RangeDecision</code> constant
	 * @throws <code>RuntimeException</code>
	 *             if the string does not match one of the constants above.
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.XMLTags
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision
	 * @see pea.modelchecking.schemas.BasicTypes.xsd
	 */
	private int getOperator(final String operator) {
		if (operator.equals(XMLTags.GREATEREQUAL_CONST)) {
			return RangeDecision.OP_GTEQ;
		} else if (operator.equals(XMLTags.GREATER_CONST)) {
			return RangeDecision.OP_GT;
		} else if (operator.equals(XMLTags.LESS_CONST)) {
			return RangeDecision.OP_LT;
		} else if (operator.equals(XMLTags.LESSEQUAL_CONST)) {
			return RangeDecision.OP_LTEQ;
		} else if (operator.equals(XMLTags.EQUAL_CONST)) {
			return RangeDecision.OP_EQ;
		} else if (operator.equals(XMLTags.NOTEQUAL_CONST)) {
			return RangeDecision.OP_NEQ;
		}
		throw new RuntimeException("Operator needs to be " + "\"" + XMLTags.GREATEREQUAL_CONST + "\", " + "\""
		        + XMLTags.GREATER_CONST + "\", " + "\"" + XMLTags.EQUAL_CONST + "\", " + "\"" + XMLTags.NOTEQUAL_CONST
		        + "\", " + "\"" + XMLTags.LESS_CONST + "\", or " + "\"" + XMLTags.LESSEQUAL_CONST + "\"");
	}

	/**
	 * Returns a <code>CDD</code> object representing the BooleanDecision for <code>booleanExpressionNode</code>. Uses
	 * <code>BooleanDecision.create</code>.
	 * 
	 * @param booleanExpressionNode
	 *            The BooleanExpression element a <code>CDD</code> needs to be constructed for
	 * @return The constructed <code>CDD</code>
	 * @throws <code>RuntimeException</code>
	 *             if the booleanExpressionNode attribute <code>expression</code> is empty, meaning
	 *             <code>expression.equals("")</code>.
	 * 
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.CDD
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision
	 * @see pea.modelchecking.schemas.BasicTypes.xsd
	 */
	private CDD createBooleanDecision(final Element booleanExpressionNode) {
		final String expression = booleanExpressionNode.getAttribute(XMLTags.EXPRESSION_TAG);
		if (expression.equals("")) {
			throw new RuntimeException("Empty expressions are not allowed");
		}
		if (expression.equals(XMLTags.TRUE_CONST)) {
			return CDD.TRUE;
		}
		if (expression.equals(XMLTags.FALSE_CONST)) {
			return CDD.FALSE;
		}
		try {
			if (expression.contains("=>")) {
				return RelationDecision.create(expression.split("=>"), Operator.GEQ);
			} else if (expression.contains(Operator.GEQ.toString())) {
				return RelationDecision.create(expression.split(Operator.GEQ.toString()), Operator.GEQ);
			} else if (expression.contains("<=")) {
				return RelationDecision.create(expression.split("<="), Operator.LEQ);
			} else if (expression.contains(Operator.LEQ.toString())) {
				return RelationDecision.create(expression.split(Operator.LEQ.toString()), Operator.LEQ);
			} else if (expression.contains(Operator.LESS.toString())) {
				return RelationDecision.create(expression.split(Operator.LESS.toString()), Operator.LESS);
			} else if (expression.contains(Operator.GREATER.toString())) {
				return RelationDecision.create(expression.split(Operator.GREATER.toString()), Operator.GREATER);
			} else if (expression.contains(Operator.NEQ.toString())) {
				return RelationDecision.create(expression.split(Operator.NEQ.toString()), Operator.NEQ);
			} else if (expression.contains(Operator.EQUALS.toString())) {
				return RelationDecision.create(expression.split(Operator.EQUALS.toString()), Operator.EQUALS);
			}
		} catch (final IllegalArgumentException e) {
			throw new IllegalArgumentException("Found wrong number of operands in " + expression);
		}

		return BooleanDecision.create(expression);
	}

	// /**
	// * Returns a <code>CDD</code> object representing the ZDecision for
	// * this method's argument.
	// *
	// * @see createBooleanDecision() above
	// * */
	// private CDD createZDecision(Element zExpressionNode) {
	// String exp = zExpressionNode.getAttribute(XMLTags.EXPRESSION_TAG);
	// if (exp.equals(""))
	// throw new RuntimeException("Empty expressions are not allowed");
	//
	// if (exp.equals(XMLTags.TRUE_CONST))
	// return CDD.TRUE;
	// if (exp.equals(XMLTags.FALSE_CONST))
	// return CDD.FALSE;
	//
	// if(exp.contains(Operator.GEQ.toString())){
	// exp = exp.replace(Operator.GEQ.toString(), ZString.GEQ);
	// }else if(exp.contains("=>")){
	// exp = exp.replace("=>", ZString.GEQ);
	// }else if(exp.contains(Operator.LEQ.toString())){
	// exp = exp.replace(Operator.LEQ.toString(), ZString.LEQ);
	// }else if(exp.contains("<=")){
	// exp = exp.replace("<=", ZString.LEQ);
	// }else if(exp.contains(Operator.LESS.toString())){
	// exp = exp.replace(Operator.LESS.toString(), ZString.LESS);
	// }else if(exp.contains(Operator.GREATER.toString())){
	// exp = exp.replace(Operator.GREATER.toString(), ZString.GREATER);
	// }else if(exp.contains(Operator.NEQ.toString())){
	// exp = exp.replace(Operator.NEQ.toString(), ZString.NEQ);
	// }else if(exp.contains(Operator.EQUALS.toString())){
	// exp = exp.replace(Operator.EQUALS.toString(), ZString.EQUALS);
	// }
	//
	// ZTerm zTerm;
	// try {
	// zTerm = ZWrapper.INSTANCE.predicateToTerm(exp);
	// } catch (ParseException e) {
	// e.printStackTrace();
	// return null;
	// } catch (InstantiationException e) {
	// e.printStackTrace();
	// return null;
	// }
	// TermToZCDDVisitor visitor =
	// new TermToZCDDVisitor(zTerm);
	// return zTerm.getTerm().accept(visitor);
	// }

	/**
	 * Returns a <code>CDD</code> object representing the RangeDecision for <code>rangeExpressionNode</code>. Uses
	 * <code>RangeDecision.create</code>.
	 * 
	 * @param rangeExpressionNode
	 *            The RangeExpression element a <code>CDD</code> needs to be constructed for
	 * @return The constructed <code>CDD</code>
	 * @throws <code>RuntimeException</code>
	 *             if the rangeExpressionNode attribute <code>variable</code> is empty, meaning
	 *             <code>variable.equals("")</code>.
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.CDD
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision
	 * @see pea.modelchecking.schemas.BasicTypes.xsd
	 */
	private CDD createRangeDecision(final Element rangeExpressionNode) {
		final String variable = rangeExpressionNode.getAttribute(XMLTags.VARIABLE_TAG);
		if (variable.equals("")) {
			throw new RuntimeException("Range expressions with empty " + "variables are not allowed");
		}

		final String operatorString = rangeExpressionNode.getAttribute(XMLTags.OPERATOR_TAG);
		final int operator = getOperator(operatorString);

		final String boundString = rangeExpressionNode.getAttribute(XMLTags.BOUND_TAG);
		final double bound = (new Double(boundString)).doubleValue();

		return RangeDecision.create(variable, operator, (int) bound);
	}

	/**
	 * Returns a <code>CDD</code> object representing the EventDecision for <code>eventNode</code>. Uses
	 * <code>EventDecision.create</code>.
	 * 
	 * @param eventNode
	 *            The EventExpression element a <code>CDD</code> needs to be constructed for
	 * @return The constructed <code>CDD</code>
	 * @throws <code>RuntimeException</code>
	 *             if the eventNode attribute <code>name</code> is empty, meaning <code>name.equals("")</code>.
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.CDD
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision
	 * @see pea.modelchecking.schemas.BasicTypes.xsd
	 */
	private CDD createEventDecision(final Element eventNode) {
		final String eventName = eventNode.getAttribute(XMLTags.NAME_Tag);
		if (eventName.equals("")) {
			throw new RuntimeException("Empty name attributes are not allowed");
		}
		return EventDecision.create(eventName);
	}

}
