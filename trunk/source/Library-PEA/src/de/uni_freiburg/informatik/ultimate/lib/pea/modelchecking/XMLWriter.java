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

import java.io.FileWriter;
import java.io.IOException;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.w3c.dom.Text;

/**
 * The class <code>XMLWriter</code> offers functionality to write the
 * XML representation of a given <code>Document</code> into a specified file.
 * 
 * @author Roland Meyer
 * @see org.w3c.dom.Document
 *  
 */
public class XMLWriter {

    /**
     * Writes the XML representation of <code>node</code> and the children of
     * <code>node</code> into a string by recursively calling this method.
     * 
     * @param node
     *            The node to be written into a string
     * @param depth
     *            The depth of the recursion. Used to indent.
     * @return The xml representation of <code>node</code> as string
     */
    private String traverse(Node node, int depth) {
        final StringBuffer sb = new StringBuffer();
        if (node.getNodeType() == Node.DOCUMENT_NODE) {
            sb.append("<?xml version=\"1.0\" encoding=\"UTF-8\"?>");
	    sb.append("\n<!DOCTYPE nta PUBLIC \"-//Uppaal Team//DTD Flat System 1.0//EN\" \"http://www.docs.uu.se/docs/rtmv/uppaal/xml/flat-1_0.dtd\">");
            for (int i = 0; i < node.getChildNodes().getLength(); i++) {
                sb.append(traverse(node.getChildNodes().item(i), 0));
            }
        }
        if (node.getNodeName().equals(XMLTags.Z_TAG)) {
            final String temp = " " + node.getTextContent();
            sb.append(temp);
        } else if (node.getNodeType() == Node.ELEMENT_NODE) {
            sb.append("\n");
            for (int i = 0; i < depth; i++) {
                sb.append("    ");
            }
            sb.append("<" + node.getNodeName());

            final NamedNodeMap attributes = node.getAttributes();
            final int attributeCount = attributes.getLength();

            for (int i = 0; i < attributeCount; i++) {
                sb.append(traverse(attributes.item(i), depth + 1));
            }

            final NodeList children = node.getChildNodes();
            final int childCount = children.getLength();

            if (childCount > 0) {
                sb.append(">");
                final boolean onlyTextChildren = elementOnlyHasTextChildren((Element) node);

                for (int i = 0; i < childCount; i++) {
                    sb.append(traverse(children.item(i), depth + 1));
                }
                if (!onlyTextChildren) {
                    sb.append("\n");
                    for (int i = 0; i < depth; i++) {
                        sb.append("    ");
                    }
                }
                sb.append("</" + node.getNodeName() + ">");
            } else {
                sb.append("/>");
            }
        } else if (node.getNodeType() == Node.TEXT_NODE) {
            if (containsData((Text) node)) {
                sb.append(node.getNodeValue());
            }
        } else if (node.getNodeType() == Node.ATTRIBUTE_NODE) {
            sb.append(" " + node.getNodeName() + " = \"" + node.getNodeValue()
                    + "\"");
        }
        return sb.toString();
    }

    /**
     * Checks whether a given <code>Text</code> object contains a letter or a
     * digit.
     * 
     * @param text
     *            The text object
     * @return <code>true</code>, if the text object contains a letter or a
     *         digit, <code>false</code> otherwise
     */
    private boolean containsData(Text text) {
        final String data = text.getData();
        for (int i = 0; i < data.length(); i++) {
            if (Character.isLetter(data.charAt(i))
                    || Character.isDigit(data.charAt(i))) {
                return true;
            }
        }
        return false;
    }

    /**
     * Checks whether a given element has only children that are
     * <code>Text</code> nodes
     * 
     * @param node
     *            Node that needs to be checked
     * @return <code>true</code> if the node has <code>Text</code> children
     *         only, <code>false</code> otherwise
     */
    private boolean elementOnlyHasTextChildren(Element node) {
        boolean result = false;
        final NodeList children = node.getChildNodes();
        final int childCount = children.getLength();
        for (int i = 0; i < childCount; i++) {
            final int nodeType = children.item(i).getNodeType();
            if (nodeType == Node.TEXT_NODE) {
                result = true;
            }
            if (nodeType == Node.ELEMENT_NODE) {
                return false;
            }
        }
        return result;
    }

    /**
     * Traverses the given <code>document</code> and writes the result into
     * the file given by <code>fileName</code>.
     * 
     * @param document
     *            The <code>Document</code> element to be written in a file.
     * @param fileName
     *            The file, where <code>document</code> shall be written
     * @throws Exception
     *             IOException, when the <code>FileWriter</code> cannot be
     *             instantiated with file <code>fileName</code> or an error
     *             occurs writing the file or closing it.
     */
    public void writeXMLDocumentToFile(Document document, String fileName)
            throws IOException {
        final FileWriter writer = new FileWriter(fileName);
        writer.write(traverse(document, 0));
        writer.flush();
        writer.close();
    }
    
    public String writeXMLDocumentToString(Element element){
    	return traverse(element, 0);
    }
}
