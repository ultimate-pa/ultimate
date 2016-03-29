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

import de.uni_muenster.cs.sev.lethal.parser.tree.*;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;

/**
 * GUI Item representing a hedge.
 * @author Philipp
 *
 */
public class HedgeItem extends AbstractTreeItem {

	/**
	 * Reads a saved HedgeItem from an XML element.
	 * @param parentElement XML element containing the serialized hedge
	 * @param project project this item will belong to.
	 * @return the loaded HedgeItem
	 * @throws ParseException raised if parsing of the serialized hedge fails.
	 * @throws TokenMgrError raised if parsing of the serialized hedge fails.
	 */
	public static HedgeItem fromXML(Element parentElement, Project project) throws ParseException, TokenMgrError{
		HedgeItem item = new HedgeItem(parentElement.getAttribute("name"), project);
		String treeString = parentElement.getTextContent().trim();
		
		if (treeString == null || treeString.length() == 0){
			item.hedge = null;
		} else {
			item.hedge = TreeParser.parseStringAsHedge(treeString);
		}
		return item;
	}
	
	/**
	 * User visible class name of this Item class.
	 * @return user visible class name of this Item class
	 */
	public static String getItemClassName(){
		return "Hedge";
	}
	
	/**
	 * Hedge encapsulated by this item.
	 */
	private Tree<UnrankedSymbol> hedge;
	
	/**
	 * Creates a new tree Item, with no hedge in it.
	 * @param name item name
	 * @param project the project this tree item belongs to
	 */
	public HedgeItem(String name, Project project){
		super(name, project);
	}
	
	/**
	 * Creates a new tree Item, containing the given hedge.
	 * @param name item name
	 * @param project the project this tree item belongs t.
	 * @param tree hedge to contain
	 */
	public HedgeItem(String name, Project project, Tree<UnrankedSymbol> tree){
		super(name, project);
		this.hedge = tree;
	}
	
	
	@Override
	public Tree<UnrankedSymbol> getTree() {
		return hedge;
	}
	
	/**
	 * Updates the hedge inside this item. An ItemEdited Project event will be raised.
	 * @param hedge new hedge to store inside this item.
	 */
	public void setHedge(Tree<UnrankedSymbol> hedge) {
		if (this.hedge != hedge){
			this.hedge = hedge;
			super.fireItemContentSet();
		}
	}

	@Override
	public Editor getEditor() {
		return new HedgeEditor(this);
	}

	@Override
	public void toXML(Element parentElement) {
		//TODO: We might want to save the tree as an XML structure
		if (this.hedge == null) return;
		parentElement.setTextContent(this.hedge.toString());
	}

}
