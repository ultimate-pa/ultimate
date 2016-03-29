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

import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.Symbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;

/**
 * Abstract superclass for tree and hedge items.
 * @author Philipp
 *
 */
public abstract class AbstractTreeItem extends Item {
	
	/**
	 * Create a new tree item matching the given tree object type. <br>
	 * Currently only TreeItem and HedgeItem are supported (from Trees with RankedSymbol resp. UnrankedSymbol type)
	 * as this is all the GUI can handle.
	 * @param name name of the item
	 * @param project project the item will belong to
	 * @param tree tree the item contains
	 * @return a Tree or HedgeItem containing the given tree
	 */
	@SuppressWarnings("unchecked")
	public static AbstractTreeItem fromTree(String name, Project project, Tree<? extends Symbol> tree){
		if (UnrankedSymbol.class.isAssignableFrom(tree.getSymbolClass())){
			return new HedgeItem(name, project,(Tree<UnrankedSymbol>)tree);
		} else if (RankedSymbol.class.isAssignableFrom(tree.getSymbolClass())) {
			return new TreeItem(name, project,(Tree<RankedSymbol>)tree);
		} else {
			throw new IllegalArgumentException();
		}
	}

	
	protected AbstractTreeItem(String name, Project project) {
		super(name, project);
	}

	/**
	 * Returns the tree contained by this Item.<br>
	 * To be implemented by subclass.
	 * @return the tree contained by this Item
	 */
	public abstract Tree<? extends Symbol> getTree();
	
	@Override
	/**
	 * @see Item#.getEditor
	 */
	public abstract Editor getEditor();

	@Override
	public abstract void toXML(Element parentElement);
}
