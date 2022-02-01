/* $Id: PEAXML2JConverterWithVarList.java 406 2009-07-09 10:44:35Z jfaber $
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

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * This simple class works basically in the same way as its superclass with the exception that it provides additional
 * methods that allows the user to get all variables that are specified in a <code>XMLTags.VARIABLE_TAG</code>.
 * 
 * @author Johannes Faber
 *
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.XMLTags
 */
@Deprecated
public class PEAXML2JConverterWithVarList extends PEAXML2JConverter {

	private static final String DEFAULT_LOGGER = "PEAJ2XMLConverterWithVarList";

	private ILogger logger = null;

	public PEAXML2JConverterWithVarList(final boolean useZ) throws Exception {
		super(useZ);
		logger = ILogger.getLogger(PEAXML2JConverterWithVarList.DEFAULT_LOGGER);
	}

	/**
	 * Got all variables from the parsed XML-document.
	 * 
	 * @return Returns an ArrayList with all variables.
	 */
	public ArrayList[] getAdditionalVariables() {
		final Document document = parser.getDocument();
		final NodeList peaNodes = document.getElementsByTagName(XMLTags.PEA_TAG);
		if (peaNodes.getLength() == 0) {
			throw new RuntimeException("PEA count = 0 is not allowed");
		}
		final ArrayList[] additionalVariables = new ArrayList[peaNodes.getLength()];
		for (int i = 0; i < additionalVariables.length; i++) {
			additionalVariables[i] = getAdditionalVariablesForPEA((Element) peaNodes.item(i), XMLTags.NAME_Tag);
		}
		return additionalVariables;
	}

	/**
	 * Got all clocks from the parsed XML-document.
	 * 
	 * @return Returns an ArrayList with all clocks.
	 */
	public ArrayList<String> getClockList() {
		final Document document = parser.getDocument();
		final NodeList peaNodes = document.getElementsByTagName(XMLTags.PEA_TAG);
		if (peaNodes.getLength() == 0) {
			throw new RuntimeException("PEA count = 0 is not allowed");
		}
		final NodeList clockNodes = document.getElementsByTagName(XMLTags.CLOCK_TAG);
		final ArrayList<String> clockList = new ArrayList<>();
		for (int i = 0; i < clockNodes.getLength(); i++) {
			clockList.add(((Element) clockNodes.item(i)).getAttribute(XMLTags.NAME_Tag));
		}
		return clockList;
	}

	/**
	 * Gets all types of variables from the parsed XML-document.
	 * 
	 * @return Returns an ArrayList with all types (in the same order as the variables).
	 */
	public ArrayList<String>[] getTypes() {
		final Document document = parser.getDocument();
		final NodeList peaNodes = document.getElementsByTagName(XMLTags.PEA_TAG);
		if (peaNodes.getLength() == 0) {
			throw new RuntimeException("PEA count = 0 is not allowed");
		}
		final ArrayList<String>[] types = new ArrayList[peaNodes.getLength()];
		for (int i = 0; i < types.length; i++) {
			types[i] = getAdditionalVariablesForPEA((Element) peaNodes.item(i), XMLTags.TYPE_TAG);
		}
		return types;
	}

	/**
	 * This method is called by <code>getTypes</code> and <code>getAdditionalVariables</code>. It computes the variables
	 * or types for a single PEA.
	 * 
	 * @param peaNode
	 *            The Element representing the PEA.
	 * @param type
	 *            A string with an attribute-name. Either <code>XMLTags.NAME_Tag</code
	 * or <code>XMLTags.TYPE_TAG</code>.
	 * @return an ArrayList with the computes variables or types.
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.XMLTags
	 */
	private ArrayList<String> getAdditionalVariablesForPEA(final Element peaNode, final String type) {
		final NodeList variableNodes = peaNode.getElementsByTagName(XMLTags.VARIABLE_TAG);
		final ArrayList<String> variablesForPEA = new ArrayList<>();
		variablesForPEA.clear();
		for (int i = 0; i < variableNodes.getLength(); i++) {
			logger.info("Variable: " + i);
			final String temp = new String(((Element) variableNodes.item(i)).getAttribute(type));
			if (!temp.equals("")) {
				logger.info("Name: " + temp);
				variablesForPEA.add(temp);
			}
		}
		return variablesForPEA;
	}

}
