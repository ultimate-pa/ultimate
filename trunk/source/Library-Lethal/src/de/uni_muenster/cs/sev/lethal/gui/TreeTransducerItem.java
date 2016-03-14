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

import de.uni_muenster.cs.sev.lethal.parser.treetransducer.*;

import de.uni_muenster.cs.sev.lethal.treetransducer.EasyTT;

/**
 * GUI item representing a tree transducer. 
 * @author Philipp
 *
 */
public class TreeTransducerItem extends Item {

	/**
	 * Loads a TreeTransducerItem from an XML element.
	 * @param parentElement XML Element to load from
	 * @param project Project the item will be part of
	 * @return the loaded TreeTransducerItem
	 * @throws ParseException thrown if a parser error occurs 
	 * @throws TokenMgrError  thrown if a parser error occurs
	 */
	public static TreeTransducerItem fromXML(Element parentElement, Project project) throws ParseException, TokenMgrError{
		String transducerDescription = parentElement.getTextContent().trim();
		String name = parentElement.getAttribute("name");
		EasyTT tt = TreeTransducerParser.parseString(transducerDescription);
		TreeTransducerItem item = new TreeTransducerItem(name, project);
		item.transducer = tt;
		item.transducerString = transducerDescription;
		return item;
	}
	
	/**
	 * Returns the user visible class name for the tree transducer items.
	 * @return the user visible class name for the tree transducer items
	 */
	public static String getItemClassName(){
		return "Tree Transducer";
	}
	
	
	private EasyTT transducer;
	private String transducerString;
	
	/**
	 * Creates a new, empty tree transducer item.
	 * @param name name of the item
	 * @param project Project this item belongs to
	 */
	public TreeTransducerItem(String name, Project project) {
		super(name, project);
	}

	@Override
	public Editor getEditor() {
		return new TreeTransducerEditor(this);
	}
	
	/**
	 * Returns the TreeTransducer stored in this item.
	 * @return the TreeTransducer stored in this item
	 */
	public EasyTT getTreeTransducer(){
		return this.transducer;
	}
	
	/**
	 * Returns the user entered string description of the tree transducer.
	 * @return the user entered string description of the tree transducer
	 */
	public String getTreeTransducerString(){
		return this.transducerString;
	}
	
	/**
	 * Update the tree transducer stored in this item.
	 * @param transducer the new tree transducer
	 * @param transducerString the user entered description of the new tree transducer
	 */
	public void setTreeTransducer(EasyTT transducer, String transducerString){
		assert(transducer != null);
		assert(transducerString != null);
		this.transducer = transducer;
		this.transducerString = transducerString;
		super.fireItemContentSet();
	}

	@Override
	public void toXML(Element parentElement) {
		if (this.transducerString == null) return; 
		parentElement.setTextContent(this.transducerString);
	}

}
