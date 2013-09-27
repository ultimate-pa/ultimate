/* $Id: Formula2NFCompiler.java 227 2006-10-19 07:29:43Z jfaber $ 
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

import java.util.ArrayList;

import org.apache.log4j.Logger;
import org.apache.log4j.PropertyConfigurator;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

/**
 * Abstract class for converting formulae in normal form. The kind of normal
 * form is given by the implementing classes. The abstract class only offers
 * basic algorithms that are needed in every normal form converter.
 * 
 * @author Roland Meyer
 */
public abstract class Formula2NFCompiler {

    protected static final String DEFAULT_LOGGER = "Formula2NFCompiler";

    protected Logger logger;

    protected Document document;

    /**
     * Initialises the Formula2NFCompiler object. Takes as parameter a string
     * that defines the loggername for the built in log4j logger. If the string
     * is empty, the default name <code>Formula2NFCompiler</code> is used. An
     * application using a Compiler object has to make sure that the logger is
     * initialised via <code>PropertyConfigurator.configure()</code>.
     * 
     * @param loggerName
     * @see Logger
     * @see PropertyConfigurator
     */
    public Formula2NFCompiler(String loggerName) {
        if (loggerName.equals("")) {
            this.logger = Logger.getLogger(Formula2NFCompiler.DEFAULT_LOGGER);
        } else {
            this.logger = Logger.getLogger(loggerName);
        }
    }

    /**
     * Initialises the Formula2NFCompiler object with the default logger.
     */
    public Formula2NFCompiler() {
        this("");
    }

    /**
     * Recursive algorithm for building a normalform for a given formula. First
     * computes normal form for children, then compares operators, if necessary
     * changes the tree and if necessary computes the normalform for the
     * children again
     * 
     * @param actNode
     *            Node in the tree to be transformed in normal form. If the node
     *            is a basic element, it is in normal form. The recursion stops.
     */
    protected void buildNF(Node actNode) {
        if (!(actNode.getNodeType() == Node.ELEMENT_NODE)) {
            this.logger.debug("No element node, returning...");
            return;
        }

        Element node = (Element) actNode;
        if (this.isFormulaElement(node)) {
            this.logger.debug("Formula node, normalising children...");
            Element[] formChildren = this.getFormulaOperands(node);
            for (int i = 0; i < formChildren.length; i++) {
                this.buildNF(formChildren[i]);
            }
            this.logger.debug("Formula node, normalising children finished, "
                    + "returning...");
            return;
        }

        //A single trace always has normal form
        if (!this.isTreeElement(node)) {
            this.logger.debug("No tree, returning...");
            return;
        }

        //Normalise children first
        Element[] children = this.getFormulaOperands(node);
        for (int i = 0; i < children.length; i++) {
            this.logger.debug("Recursion, building NF for child[" + i + "]");
            this.buildNF(children[i]);
            this.logger.debug("Recursion, building NF for child[" + i
                    + "] finished");
        }

        //An or-node with children in normal form is in normal form as well
        if (node.getAttribute(XMLTags.OPERATOR_TAG).equals(XMLTags.OR_CONST)) {
            this.logger
                    .debug("\"" + XMLTags.OR_CONST + "\"-node, returning...");
            return;
        }

        boolean changed = true;
        while (changed) {

            changed = false;

            children = this.getFormulaOperands(node);
            for (int i = 0; i < children.length && !changed; i++) {

                if (this.isBasicElement(children[i])) {
                    this.logger.debug("No Tree Node, continuing...");
                    continue;
                }

                if (node.getAttribute(XMLTags.OPERATOR_TAG).startsWith(
                        XMLTags.SYNC_PREFIX)
                        && children[i].getAttribute(XMLTags.OPERATOR_TAG)
                                .equals(XMLTags.OR_CONST)) {
                    this.logger.debug("Case 1: Node sync-event, child "
                            + XMLTags.OR_CONST);
                    this.changeNodeSyncChildOr(node, children, i);
                    changed = true;

                } else if (node.getAttribute(XMLTags.OPERATOR_TAG).startsWith(
                        XMLTags.SYNC_PREFIX)
                        && children[i].getAttribute(XMLTags.OPERATOR_TAG)
                                .equals(XMLTags.AND_CONST)) {
                    this.logger.debug("Case 2: Node sync-event, child "
                            + XMLTags.AND_CONST);
                    this.changeNodeSyncChildAnd(node, children, i);
                    changed = true;

                } else if (node.getAttribute(XMLTags.OPERATOR_TAG).equals(
                        XMLTags.AND_CONST)
                        && children[i].getAttribute(XMLTags.OPERATOR_TAG)
                                .equals(XMLTags.OR_CONST)) {
                    this.logger.debug("Case 3: Node " + XMLTags.AND_CONST
                            + ", child " + XMLTags.OR_CONST);
                    this.changeNodeAndChildOr(node, children, i);
                    changed = true;
                } else if (node.getAttribute(XMLTags.OPERATOR_TAG).equals(
                        XMLTags.NOT_CONST)
                        && children[i].getAttribute(XMLTags.OPERATOR_TAG)
                                .equals(XMLTags.OR_CONST)) {
                    this.logger.debug("Case 4: Node " + XMLTags.NOT_CONST
                            + ", child " + XMLTags.OR_CONST);
                    this.changeNodeNotChildOr(node, children[i]);
                    changed = true;
                } else if (node.getAttribute(XMLTags.OPERATOR_TAG).equals(
                        XMLTags.NOT_CONST)
                        && children[i].getAttribute(XMLTags.OPERATOR_TAG)
                                .equals(XMLTags.AND_CONST)) {
                    this.logger.debug("Case 5: Node " + XMLTags.NOT_CONST
                            + ", child " + XMLTags.AND_CONST);
                    this.changeNodeNotChildAnd(node, children[i]);
                    changed = true;
                }

            }

            this.logger.debug("Changed = " + changed);
            if (changed) {
                children = this.getFormulaOperands(node);
                for (int j = 0; j < children.length; j++) {
                    this.buildNF(children[j]);
                }
            }
        }
    }

    /**
     * Changes the formula tree according to de Morgan's law for AND.
     * 
     * @param node
     *            Given tree element with operator NOT
     * @param child
     *            Given child with operator AND
     */
    protected void changeNodeNotChildAnd(Element node, Element child) {
        node.setAttribute(XMLTags.OPERATOR_TAG, XMLTags.OR_CONST);
        this.appendGrandChildrenDeMorgan(node, child);
    }

    /**
     * Changes the formula tree according to de Morgan's law for OR.
     * 
     * @param node
     *            Given tree element with operator NOT
     * @param child
     *            Given child with operator OR
     */
    protected void changeNodeNotChildOr(Element node, Element child) {
        node.setAttribute(XMLTags.OPERATOR_TAG, XMLTags.AND_CONST);
        this.appendGrandChildrenDeMorgan(node, child);
    }

    /**
     * Given node gets new inverted children
     * 
     * @param node
     *            Given tree element with operator NOT
     * @param child
     *            Given child
     */
    protected void appendGrandChildrenDeMorgan(Element node, Element child) {
        Element[] grandChildren = this.getFormulaOperands(child);
        for (int i = 0; i < grandChildren.length; i++) {
            Element newNotNode = this.getNewTreeElement();
            newNotNode.setAttribute(XMLTags.OPERATOR_TAG, XMLTags.NOT_CONST);
            newNotNode.appendChild(grandChildren[i]);
            node.appendChild(newNotNode);
        }
    }

    /**
     * Changes the formula tree according to the distributivity between CHOP and
     * disjunction
     * 
     * @param node
     *            Given tree element with operator SYNC
     * @param child
     *            Given children
     * @param childIndex
     *            Index of child element with operator OR
     */
    protected void changeNodeSyncChildOr(Element node, Element[] children,
            int childIndex) {
        Element[] orChildren = this.getFormulaOperands(children[childIndex]);
        String syncEvent = node.getAttribute(XMLTags.OPERATOR_TAG);
        node.setAttribute(XMLTags.OPERATOR_TAG, XMLTags.OR_CONST);
        children[childIndex].setAttribute(XMLTags.OPERATOR_TAG, syncEvent);

        Element newSyncNode = this.getNewTreeElement();
        newSyncNode.setAttribute(XMLTags.OPERATOR_TAG, syncEvent);

        int notI = (childIndex == 0) ? 1 : 0;
        Node clone = children[notI].cloneNode(true);

        if (childIndex == 0) {
            children[0].appendChild(clone);
            newSyncNode.appendChild(orChildren[1]);
            newSyncNode.appendChild(children[1]);
            node.appendChild(newSyncNode);
        } else {
            children[1].insertBefore(clone, orChildren[0]);
            newSyncNode.appendChild(children[0]);
            newSyncNode.appendChild(orChildren[0]);
            node.insertBefore(newSyncNode, children[1]);
        }
    }

    /**
     * Distributivity of Sync and Conjunction needs to be implemented in
     * inheriting classes.
     * 
     * @param node
     *            Given tree element with operator SYNC
     * @param child
     *            Given children
     * @param childIndex
     *            Given index of child with operator AND
     * 
     * @see TestForm2MCFormCompiler
     */
    protected abstract void changeNodeSyncChildAnd(Element node,
            Element[] children, int childIndex);

    /**
     * Distributivity of conjunction and disjunction
     * 
     * @param node
     *            Given tree element with operator AND
     * @param child
     *            Given children
     * @param childIndex
     *            Given index of child with operator OR
     */
    protected void changeNodeAndChildOr(Element node, Element[] children,
            int childIndex) {
        int negChildIndex = childIndex == 0 ? 1 : 0;

        Element[] orChildren = this.getFormulaOperands(children[childIndex]);

        Element newAndNode = this.getNewTreeElement();
        newAndNode.setAttribute(XMLTags.OPERATOR_TAG, XMLTags.AND_CONST);
        newAndNode.appendChild(orChildren[1]);
        newAndNode.appendChild(children[negChildIndex]);

        Node clone = children[negChildIndex].cloneNode(true);

        children[childIndex].setAttribute(XMLTags.OPERATOR_TAG,
                XMLTags.AND_CONST);
        children[childIndex].appendChild(clone);

        node.appendChild(newAndNode);
        node.setAttribute(XMLTags.OPERATOR_TAG, XMLTags.OR_CONST);
    }

    /**
     * Delivers operands for a given formula tree element. Raises an exception
     * if the number of operands for a given operator is not valid.
     * 
     * @param formula,
     *            The formula tree element
     * @return Element[] The operands of the given formula
     */
    protected Element[] getFormulaOperands(Element formula) {
        ArrayList<Element> result = new ArrayList<Element>();
        NodeList children = formula.getChildNodes();
        int childrenCount = children.getLength();
        for (int i = 0; i < childrenCount; i++) {
            Node actChild = children.item(i);
            if (this.isBasicElement(actChild) || this.isTreeElement(actChild)) {
                result.add((Element)actChild);
            }
        }
        if (result.size() == 0 && this.isTreeElement(formula)) {
            throw new RuntimeException(
                    "A formula tree with operand count = 0 is not allowed.");
        }
        if (formula.getAttribute(XMLTags.OPERATOR_TAG)
                .equals(XMLTags.NOT_CONST)
                && result.size() != 1) {
            throw new RuntimeException("A formula with operator "
                    + XMLTags.NOT_CONST + " has to have exactly one operand");
        }
        return (Element[]) result.toArray(new Element[result.size()]);
    }

    /**
     * Computes the binary representation of a given formula tree. Recursive
     * Algorithm: first computes the binary representation of all children and
     * then bottom-up the binary representation of <code>element</code>
     * 
     * @param element
     *            The element the binary representation needs to be computed
     *            for.
     */
    protected void makeBinary(Element element) {
        Element[] children = this.getFormulaOperands(element);
        for (int i = 0; i < children.length; i++) {
            this.makeBinary(children[i]);
        }

        if (!this.isTreeElement(element)) {
            this.logger.debug("No formula tree, returning...");
            return;
        }

        String operator = element.getAttribute(XMLTags.OPERATOR_TAG);
        if (!this.isCorrectOperator(operator)) {
            throw new RuntimeException("Operator " + operator
                    + " may not be used.");
        }

        Element actFormulaTree = element;
        Element previousFormulaTree = null;
        for (int i = 1; i < children.length - 1; i++) {
            previousFormulaTree = actFormulaTree;
            actFormulaTree = this.getNewTreeElement();
            actFormulaTree.setAttribute(XMLTags.OPERATOR_TAG, operator);
            actFormulaTree.appendChild(children[i]);
            previousFormulaTree.appendChild(actFormulaTree);
        }
        actFormulaTree.appendChild(children[children.length - 1]);
    }

    /**
     * The type of formula handled with the methods above depends on the
     * inheriting class. The following methods are used above and need to be
     * implemented.
     */
    protected abstract Element getNewTreeElement();

    protected abstract boolean isTreeElement(Node node);

    protected abstract boolean isBasicElement(Node node);

    protected abstract boolean isFormulaElement(Node node);

    protected abstract boolean isCorrectOperator(String operator);
}
