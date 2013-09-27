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
package pea.modelchecking;

import java.util.ArrayList;

import org.apache.log4j.Logger;
import org.w3c.dom.Document;
import org.w3c.dom.NodeList;
import org.w3c.dom.Element;

/**
 * This simple class works basically in the same way as its superclass with
 * the exception that it provides additional methods that allows the user
 * to get all variables that are specified in a <code>XMLTags.VARIABLE_TAG</code>.
 * @author Johannes Faber
 *
 * @see pea.modelchecking.XMLTags
 */
@Deprecated
public class PEAXML2JConverterWithVarList extends PEAXML2JConverter {

	private static final String DEFAULT_LOGGER = "PEAJ2XMLConverterWithVarList";

	private Logger logger = null;
	
	public PEAXML2JConverterWithVarList(boolean useZ) throws Exception {
		super(useZ);
		this.logger = Logger.getLogger(PEAXML2JConverterWithVarList.DEFAULT_LOGGER);
	}

	/**
	 * Got all variables from the parsed XML-document.
	 * @return Returns an ArrayList with all variables.
	 */
	public ArrayList[] getAdditionalVariables() {
		Document document = this.parser.getDocument();
		NodeList peaNodes = document.getElementsByTagName(XMLTags.PEA_TAG);
        if (peaNodes.getLength() == 0) {
            throw new RuntimeException("PEA count = 0 is not allowed");
        }		
		ArrayList[] additionalVariables = new ArrayList[peaNodes.getLength()];
		for (int i = 0; i < additionalVariables.length; i++) {
			additionalVariables[i] = getAdditionalVariablesForPEA((Element)peaNodes.item(i),
					  											  XMLTags.NAME_Tag);
		}
		return additionalVariables;
	}
	
	/**
	 * Got all clocks from the parsed XML-document.
	 * @return Returns an ArrayList with all clocks.
	 */
	public ArrayList<String> getClockList() {
		Document document = this.parser.getDocument();
		NodeList peaNodes = document.getElementsByTagName(XMLTags.PEA_TAG);
        if (peaNodes.getLength() == 0) {
            throw new RuntimeException("PEA count = 0 is not allowed");
        }
		NodeList clockNodes = document.getElementsByTagName(XMLTags.CLOCK_TAG);
		ArrayList<String> clockList = new ArrayList<String>();
		for (int i = 0; i < clockNodes.getLength(); i++) {
			clockList.add(((Element)clockNodes.item(i))
						  .getAttribute(XMLTags.NAME_Tag));
		}
		return clockList;
	}


	/**
	 * Gets all types of variables from the parsed XML-document.
	 * @return Returns an ArrayList with all types (in the same order as the variables).
	 */
	public ArrayList[] getTypes() {
		Document document = this.parser.getDocument();
		NodeList peaNodes = document.getElementsByTagName(XMLTags.PEA_TAG);
        if (peaNodes.getLength() == 0) {
            throw new RuntimeException("PEA count = 0 is not allowed");
        }
		ArrayList[] types = new ArrayList[peaNodes.getLength()];
		for (int i = 0; i < types.length; i++) {
			types[i] = getAdditionalVariablesForPEA((Element)peaNodes.item(i),
																  XMLTags.TYPE_TAG);
		}
		return types;
	}
	
	/**
	 * This method is called by <code>getTypes</code> and <code>getAdditionalVariables</code>.
	 * It computes the variables or types for a single PEA.
	 * 
	 * @param peaNode The Element representing the PEA.
	 * @param type A string with an attribute-name. Either <code>XMLTags.NAME_Tag</code
	 * or <code>XMLTags.TYPE_TAG</code>.
	 * @return an ArrayList with the computes variables or types.
	 * 
	 * @see pea.modelchecking.XMLTags
	 */
	private ArrayList getAdditionalVariablesForPEA(Element peaNode, String type) {
		   NodeList variableNodes = peaNode.getElementsByTagName(XMLTags.VARIABLE_TAG);
	       ArrayList<String> variablesForPEA = new ArrayList<String>();
	       variablesForPEA.clear();
		   for (int i = 0; i < variableNodes.getLength(); i++) {
	        	logger.info("Variable: " + i);
	        	String temp = new String(((Element)variableNodes.item(i))
										             .getAttribute(type));
	        	if(!temp.equals("")){
	        		logger.info("Name: " + temp);
	        		variablesForPEA.add(temp);
	        	}
	        }
		return variablesForPEA;
	}

	
}
