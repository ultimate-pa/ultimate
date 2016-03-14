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

import java.util.HashSet;

import org.w3c.dom.Element;

import de.uni_muenster.cs.sev.lethal.hedgeautomaton.EasyHedgeAutomaton;

import de.uni_muenster.cs.sev.lethal.parser.hedgeautomaton.HedgeAutomatonParser;
import de.uni_muenster.cs.sev.lethal.parser.hedgegrammar.HedgeGrammarParser;

import de.uni_muenster.cs.sev.lethal.hedgeautomaton.HedgeRule;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;

/**
 * GUI Item representing a finite tree automaton.
 * @author Philipp
 *
 */
public class HedgeAutomatonItem extends AbstractTreeAutomatonItem {

	/**
	 * Loads a HedgeAutomatonItem from the given XML Element.
	 * @param parentElement XML Element to load the item from
	 * @param project project the HedgeAutomatonItem will be part of
	 * @return the loaded Item
	 * @throws de.uni_muenster.cs.sev.lethal.parser.hedgegrammar.ParseException thrown if a parser error occurs while loading.
	 * @throws de.uni_muenster.cs.sev.lethal.parser.hedgeautomaton.ParseException  thrown if a parser error occurs while loading.
	 */
	public static HedgeAutomatonItem fromXML(Element parentElement, Project project) throws de.uni_muenster.cs.sev.lethal.parser.hedgegrammar.ParseException, de.uni_muenster.cs.sev.lethal.parser.hedgeautomaton.ParseException{
		HedgeAutomatonItem item = new HedgeAutomatonItem(parentElement.getAttribute("name"), project);

		String sinputmode = parentElement.getAttribute("inputmode");
		String rulesString = parentElement.getTextContent().trim();

		item.inputMode = (sinputmode.length() > 0 ? Integer.valueOf(sinputmode) : INPUT_MODE_RULES);

		if (item.inputMode == INPUT_MODE_GRAMMAR){
			item.automaton = HedgeGrammarParser.parseString(rulesString).getHA();
		} else {
			item.automaton = HedgeAutomatonParser.parseString(rulesString);
		}
		item.automatonString = rulesString;

		return item;
	}

	/**
	 * User visible class name for Hedge automaton items.
	 * @return the user visible class name for Hedge automaton items.
	 */
	public static String getItemClassName(){
		return "Hedge Automaton";
	}

	/** Represented tree automaton */
	private EasyHedgeAutomaton automaton;

	/** User entered string representation of the automaton */
	private String automatonString;

	/**
	 * Creates a new FTA Item with an empty (no rules) finite tree automaton.
	 * @param name user visible, project unique name of the item
	 * @param project project this item belongs to
	 */
	public HedgeAutomatonItem(String name, Project project){
		super(name, project);
		this.automaton = new EasyHedgeAutomaton(new HashSet<State>(), new HashSet<State>(), new HashSet<HedgeRule<UnrankedSymbol,State>>()); //start with an empty automaton
		this.automatonString = "";
	}

	/**
	 * Creates a new FTA Item with a given finite tree automaton.
	 * @param name user visible, project unique name of the item
	 * @param project project this item belongs to
	 * @param automaton finite tree automaton in this item
	 * @param automatonString User entered representation of the automaton 
	 */
	public HedgeAutomatonItem(String name, Project project, EasyHedgeAutomaton automaton, String automatonString){
		super(name, project);
		this.automaton = automaton;
		this.automatonString = automatonString;
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.gui.Item#getEditor()
	 */
	@Override
	public Editor getEditor() {
		return new HedgeAutomatonEditor(this);
	}

	/**
	 * Gets the represented automaton.
	 * @return represented automaton
	 */
	public EasyHedgeAutomaton getAutomaton() {
		return automaton;
	}


	/**
	 * Returns the user entered string representation automaton.
	 * @return the user entered string representation automaton
	 */
	public String getAutomatonString() {
		return this.automatonString;
	}

	/**
	 * Sets automaton to be represented.
	 * @param automaton automaton to be represented
	 * @param automatonString user entered string description of the automaton
	 * @param inputMode input mode of the automaton. Valid values are INPUT_MODE_RULES and INPUT_MODE_GRAMMAR.
	 */
	public void setAutomaton(EasyHedgeAutomaton automaton, String automatonString, int inputMode) {
		assert(automaton != null);
		if (this.automaton != automaton || !this.automatonString.equals(automatonString) || this.inputMode != inputMode){
			this.automaton = automaton;
			this.automatonString = automatonString;
			this.inputMode = inputMode;
			super.fireItemContentSet();
		}
	}

	@Override
	public void toXML(Element parentElement){
		parentElement.setTextContent(this.automatonString);
		parentElement.setAttribute("inputmode", String.valueOf(this.inputMode));
	}
}
