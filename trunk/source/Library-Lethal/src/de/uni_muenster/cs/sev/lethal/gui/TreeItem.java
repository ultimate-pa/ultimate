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
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;

/**
 * GUI item representing a tree.
 * @author Philipp
 */
public class TreeItem extends AbstractTreeItem {

	/**
	 * Loads a TreeItem from an XML Element.
	 * @param parentElement XML element to load from
	 * @param project project the item will be part of
	 * @return the loaded TreeItem
	 * @throws ParseException thrown if a parser error occurs 
	 * @throws TokenMgrError thrown if a parser error occurs
	 */
	public static TreeItem fromXML(Element parentElement, Project project) throws ParseException, TokenMgrError{
		TreeItem item = new TreeItem(parentElement.getAttribute("name"), project);		
		String treeString = parentElement.getTextContent().trim();

		if (treeString == null || treeString.length() == 0){
			item.tree = null;
		} else {
			item.tree = TreeParser.parseString(treeString);
		}
		return item;
	}

	/**
	 * User visible class name of this Item class
	 * @return user visible class name of this Item class
	 */
	public static String getItemClassName(){
		return "Tree";
	}

	private Tree<RankedSymbol> tree;

	/**
	 * Create a new tree item.
	 * @param name item name
	 * @param project the project this tree item belongs to
	 */
	public TreeItem(String name, Project project){
		super(name, project);
	}

	/**
	 * Creates a new tree item.
	 * @param name item name
	 * @param project the project this tree item belongs to
	 * @param tree tree stored in this item.
	 */
	public TreeItem(String name, Project project, Tree<RankedSymbol> tree){
		super(name, project);
		this.tree = tree;
	}

	@Override
	public Tree<RankedSymbol> getTree() {
		return tree;
	}

	/**
	 * Update the tree stored in this item.
	 * @param tree new tree to store in this item
	 */
	public void setTree(Tree<RankedSymbol> tree) {
		if (this.tree != tree){
			this.tree = tree;
			super.fireItemContentSet();
		}
	}

	@Override
	public Editor getEditor() {
		return new TreeEditor(this);
	}

	@Override
	public void toXML(Element parentElement) {
		//TODO: We might want to save the tree as an XML structure
		if (this.tree == null) return;
		parentElement.setTextContent(this.tree.toString());
	}

}
