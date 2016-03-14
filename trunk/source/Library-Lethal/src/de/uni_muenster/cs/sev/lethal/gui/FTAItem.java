/*
 * Copyright 2009 Dorothea Jansen <d.jansen@uni-muenster.de>, Martin Mohr <mohrfrosch@uni-muenster.de>, Irene Thesing <i_thes01@uni-muenster.de>, Anton Reis <antonreis@gmx.de>, Maria Schatz <m_scha17@uni-muenster.de>, Philipp Claves <philipp.claves@uni-muenster.de>, Sezar Jarrous <sezar.jarrous@gmail.com>
 *
 * This file is part of LETHAL.
 *
 * LETHAL is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * LETHAL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with LETHAL.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_muenster.cs.sev.lethal.gui;

import org.w3c.dom.Element;
import org.w3c.dom.Node;

import de.uni_muenster.cs.sev.lethal.parser.fta.FTAParser;
import de.uni_muenster.cs.sev.lethal.parser.fta.ParseException;
import de.uni_muenster.cs.sev.lethal.parser.ftagrammar.FTAGrammarParser;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTA;

/**
 * GUI Item representing a finite tree automaton.
 * @author Philipp
 *
 */
public class FTAItem extends AbstractTreeAutomatonItem {
	
	/**
	 * Reads a saved FTAItem from an XML element .
	 * @param parentElement XML element containing the serialized automaton
	 * @param project project this item will belong to.
	 * @return the loaded FTAItem
	 * @throws ParseException raised if parsing of the serialized FTA fails.
	 * @throws de.uni_muenster.cs.sev.lethal.parser.ftagrammar.ParseException  raised if parsing of the serialized FTA fails.
	 */
	public static FTAItem fromXML(Element parentElement, Project project) throws ParseException, de.uni_muenster.cs.sev.lethal.parser.ftagrammar.ParseException{
		FTAItem item = new FTAItem(parentElement.getAttribute("name"), project);
		
		if (parentElement.getTextContent().trim().length() == 0){
			StringBuffer rulesString = new StringBuffer();
			for (int i = 0; i < parentElement.getChildNodes().getLength(); i++){
				Node ruleElement = parentElement.getChildNodes().item(i);
				rulesString.append(ruleElement.getTextContent());
				rulesString.append("\n");
			}
			item.automatonString = rulesString.toString();
		} else {
			item.automatonString = parentElement.getTextContent().trim();
		}
		
		String sinputmode = parentElement.getAttribute("inputmode");
		item.inputMode = (sinputmode.length() > 0 ? Integer.valueOf(sinputmode) : INPUT_MODE_RULES);
		
		if (item.inputMode == INPUT_MODE_GRAMMAR){
			item.automaton = FTAGrammarParser.parseString(item.automatonString);
		} else {
			item.automaton = FTAParser.parseString(item.automatonString);
		}
		
		return item;
	}
	
	/**
	 * User readable class name of the FTAItems.
	 * @return the readable class name of the FTAItems.
	 */
	public static String getItemClassName(){
		return "Finite Tree Automaton";
	}

	/** Represented tree automaton. */
	private EasyFTA automaton;
	
	/** User entered string representation of the automaton. */
	private String automatonString;
	
	/**
	 * Create a new FTA Item with an empty (no rules) finite tree automaton.
	 * @param name user visible, project unique name of the item
	 * @param project Project this item belongs to
	 */
	public FTAItem(String name, Project project){
		super(name, project);
		this.automaton = new EasyFTA(); //start with an empty automaton
	}
	
	/**
	 * Create a new FTA Item with a given finite tree automaton.
	 * @param name user visible, project unique name of the item
	 * @param project project this item belongs to
	 * @param automaton finite tree automaton in this item 
	 * @param automatonString user entered string description of the finite tree automaton 
	 * (input in RULES mode assumed!)
	 */
	public FTAItem(String name, Project project, EasyFTA automaton, String automatonString){
		super(name, project);
		this.automaton = automaton;
		this.automatonString = automatonString;
	}
	
	/**
	 * @see de.uni_muenster.cs.sev.lethal.gui.Item#getEditor()
	 */
	@Override
	public Editor getEditor() {
		return new FTAEditor(this);
	}
	
	/**
	 * Gets the represented automaton.
	 * @return represented automaton
	 */
	public EasyFTA getAutomaton() {
		return automaton;
	}
	
	/**
	 * Returns the string representation of the FTA in this item.
	 * @return the string representation of the FTA in this item
	 */
	public String getAutomatonString(){
		return automatonString;
	}
	
	/**
	 * Sets automaton to be represented.
	 * @param automaton automaton to be represented
	 * @param automatonString user entered string description of the finite tree automaton
	 * @param inputMode input mode of the FTA. Valid values are INPUT_MODE_RULES and INPUT_MODE_GRAMMAR.
	 */
	public void setAutomaton(EasyFTA automaton, String automatonString, int inputMode) {
		assert(automaton != null);
		if (this.automaton != automaton || this.automatonString != automatonString || this.inputMode != inputMode){
			this.automaton = automaton;
			this.automatonString = automatonString;
			this.inputMode = inputMode;
			super.fireItemContentSet();
		}
	}
	
	@Override
	public void toXML(Element parentElement){
		if (this.automaton == null) return;
		parentElement.setTextContent(this.automatonString);
		parentElement.setAttribute("inputmode", String.valueOf(this.inputMode));
	}
}
