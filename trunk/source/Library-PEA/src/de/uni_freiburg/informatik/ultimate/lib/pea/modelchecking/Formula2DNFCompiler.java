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

import org.apache.xerces.dom.DocumentImpl;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;


/**
 * @author Roland Meyer
 *
 * Computes the disjunctive normal form for a formula given as
 * <code>Formula</code> element.
 * 
 * @see <code>BasicTypes.xsd</code>
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.Formula2NFCompiler
 */
public class Formula2DNFCompiler extends Formula2NFCompiler {

    
    /**
     * There are no sync events in formulae for guards, invariants, or
     * clock invariants. If this method is called, an exception is raised.
     * 
     * @param node The node to be handled
     * @param children The children to be handled
     * 
     * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.Formula2NFCompiler
     */
    @Override
	protected void changeNodeSyncChildAnd(Element node, Element[] children,
            int childIndex) {
        throw new RuntimeException(
                "A formula that is no testformula is not allowed "
                        + "to have sync events");
    }
    
    /**
     * There are no sync events in formulae for guards, invariants, or
     * clock invariants. If this method is called, an exception is raised.
     * 
     * @param node The node to be handled
     * @param children The children to be handled
     * 
     * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.Formula2NFCompiler
     */
    @Override
	protected void changeNodeSyncChildOr(Element node, Element[] children,
            int childIndex) {
        throw new RuntimeException("A formula in guards, invariants, "
                + "or clockinvariants" + " may not have sync events");
    }
    
    /**
     * Returns a new <code>FormulaTree</code>-Element.
     * 
     * @return The new tree element.
     * 
     * @see <code>BasicTypes.xsd</code>
     */
    @Override
	protected Element getNewTreeElement() {
        return document.createElement(XMLTags.FORMULATREE_TAG);
    }

    /**
     * A given node is a tree element, if it has the <code>formulaTree</code>-Tag.
     * 
     * @param node, the node to be checked
     * @return true, if the tag is <code>formulaTree</code>
     * 
     * @see <code>BasicTypes.xsd</code>
     */
    @Override
	protected boolean isTreeElement(Node node) {
        return node.getNodeName().equals(XMLTags.FORMULATREE_TAG);
    }

    /**
     * A given node is a basic element, if it has the <code>[...]Expression</code>-Tag.
     * 
     * @param node, the node to be checked
     * @return true, if the tag is <code>[...]Expression</code>
     * 
     * @see <code>BasicTypes.xsd</code>
     */
    @Override
	protected boolean isBasicElement(Node node) {
        final String nodeName = node.getNodeName();
        return nodeName.equals(XMLTags.BOOLEANEXPRESSION_TAG)
                || nodeName.equals(XMLTags.EVENTEXPRESSION_TAG)
                || nodeName.equals(XMLTags.RANGEEXPRESSION_TAG);
    }

    /**
     * A given node is a tree element, if it has a <code>invariant</code>, <code>clockInvariant</code>-, or <code>guard</code>-Tag.
     * 
     * @param node, the node to be checked
     * @return true, if the tag is of the desired form.
     * 
     */
    @Override
	protected boolean isFormulaElement(Node node) {
        final String nodeName = node.getNodeName();
        return nodeName.equals(XMLTags.INVARIANT_TAG)
                || nodeName.equals(XMLTags.CLOCKINVARIANT_TAG)
                || nodeName.equals(XMLTags.GUARD_TAG);
    }

    /**
     * Only OR, AND, NOT are allowed in formulae to be converted to disjunctive
     * normal form.
     * 
     * @param operator, the operator to be checked
     * @return true, if the operator is OR, AND, or NOT
     * 
     * @see <code>BasicTypes.xsd</code>
     */
    @Override
	protected boolean isCorrectOperator(String operator) {
        return operator.equals(XMLTags.OR_CONST)
                || operator.equals(XMLTags.AND_CONST)
                || operator.equals(XMLTags.NOT_CONST);
    }

    /**
     * Computes the disjunctive normal form for a given formula. Makes it binary
     * first, then computes the normal form, and finally makes it n-ary again.
     * 
     * @param formula, The formula to be converted to disjunctive normal form.
     * @return Element, The formula in disjunctive normal form.
     * 
     * @see <code>BasicTypes.xsd</code>
     * @see Formula2NFCompiler
     */
    public Element compile(Element formula) {
        document = new DocumentImpl();
        final Element formulaNode = (Element) document.importNode(formula, true);
        document.appendChild(formulaNode);
        makeBinary(formulaNode);
        buildNF(formulaNode);
        makeNAry(formulaNode);
        return formulaNode;
    }

    /**
     * Computes the n-ary representation of a formula
     * 
     * @param formula The formula to be transformed into n-ary representation.
     * 
     * @see <code>BasicTypes.xsd</code>
     */
    
    protected void makeNAry(Element formula) {
        if (!isBasicElement(formula) && !isTreeElement(formula)
                && !isFormulaElement(formula)) {
            throw new RuntimeException("A formula may only contain a tag "
                    + "indicating formula type, tree elements, "
                    + "and basic elements");
        }

        if (isBasicElement(formula)) {
            logger.debug("Elementary element, returning...");
            return;
        }

        final Element[] children = getFormulaOperands(formula);
        for (int i = 0; i < children.length; i++) {
            makeNAry(children[i]);
            if ((formula.getAttribute(XMLTags.OPERATOR_TAG).equals(
                    XMLTags.OR_CONST) && children[i].getAttribute(
                    XMLTags.OPERATOR_TAG).equals(XMLTags.OR_CONST))
                    || (formula.getAttribute(XMLTags.OPERATOR_TAG).equals(
                            XMLTags.AND_CONST) && children[i].getAttribute(
                            XMLTags.OPERATOR_TAG).equals(XMLTags.AND_CONST))) {
                final Element[] grandChildren = getFormulaOperands(children[i]);
                for (int j = 0; j < grandChildren.length; j++) {
                    formula.appendChild(grandChildren[j]);
                }
                formula.removeChild(children[i]);
            } else if (formula.getAttribute(XMLTags.OPERATOR_TAG).equals(
                    XMLTags.NOT_CONST)
                    && children[i].getAttribute(XMLTags.OPERATOR_TAG).equals(
                            XMLTags.NOT_CONST)) {
                final Node formParent = formula.getParentNode();
                final Element[] grandChildren = getFormulaOperands(children[i]);
                formParent.replaceChild(grandChildren[0], formula);
            }
        }
    }

    /**
     * This method transforms all formulas occuring in Phase Event Automata
     * to DNF.
     * @param autDoc The (XML-)document representing the PEA's in which the
     * formulas have to be transformed.
     */
	public void compile(Document autDoc) {
        final NodeList sInvs = autDoc.getElementsByTagName(XMLTags.INVARIANT_TAG);
        final int sInvCount = sInvs.getLength();
        for (int i = 0; i < sInvCount; i++) {
        	logger.info("Converting formula "+i + "/" + sInvCount);
        
            final Element form = this.compile((Element) sInvs.item(i));
            final Element newForm = (Element) autDoc.importNode(form, true);
            final Node sInvParent = sInvs.item(i).getParentNode();
            sInvParent.replaceChild(newForm, sInvs.item(i));
        }
        logger.info("Finished!");
        

        final NodeList clockInvs = autDoc
                .getElementsByTagName(XMLTags.CLOCKINVARIANT_TAG);
        final int clockInvCount = clockInvs.getLength();
        
        for (int i = 0; i < clockInvCount; i++) {
        	logger.info("Converting clockinvariant "+i + "/" + clockInvCount);
            final Element form = this.compile((Element) clockInvs.item(i));
            final Element newForm = (Element) autDoc.importNode(form, true);
            final Node clockInvParent = clockInvs.item(i).getParentNode();
            clockInvParent.replaceChild(newForm, clockInvs.item(i));
        }
        logger.info("Finished!");

    	
        final NodeList guards = autDoc.getElementsByTagName(XMLTags.GUARD_TAG);
        final int guardCount = guards.getLength();
        for (int i = 0; i < guardCount; i++) {
        	logger.info("Converting guard "+i + "/" + guardCount)	;
            final Element form = this.compile((Element) guards.item(i));
            final Element newForm = (Element) autDoc.importNode(form, true);
            final Node guardParent = guards.item(i).getParentNode();
            guardParent.replaceChild(newForm, guards.item(i));
        }
        logger.info("Finished!");
	}
    
   
}
