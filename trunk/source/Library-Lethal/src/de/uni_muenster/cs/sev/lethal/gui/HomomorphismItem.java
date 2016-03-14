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

import de.uni_muenster.cs.sev.lethal.hom.EasyHom;

import org.w3c.dom.Element;

import de.uni_muenster.cs.sev.lethal.parser.homomorphism.HomomorphismParser;
import de.uni_muenster.cs.sev.lethal.parser.homomorphism.ParseException;
import de.uni_muenster.cs.sev.lethal.parser.homomorphism.TokenMgrError;

/**
 * GUI item that Encapsulates a tree homomorphism.
 * @author Philipp
 *
 */
public class HomomorphismItem extends Item {

	/**
	 * Loads a HomomorphismItem from the given XML Element.
	 * @param parentElement XML Element to load the item from
	 * @param project Project the HomomorphismItem will be part of
	 * @return the loaded item
	 * @throws ParseException thrown if a parser error occurs while loading
	 * @throws TokenMgrError  thrown if a parser error occurs while loading
	 */
	public static HomomorphismItem fromXML(Element parentElement, Project project) throws ParseException, TokenMgrError{
		String homomorphismDescription = parentElement.getTextContent().trim();
		String name = parentElement.getAttribute("name");
		EasyHom hom = HomomorphismParser.parseString(homomorphismDescription);
		HomomorphismItem item = new HomomorphismItem(name,project);
		item.homomorphism = hom;
		item.homomorphismString = homomorphismDescription;
		return item;
	}
	
	/**
	 * Returns the user visible class name for homomorphism items.
	 * @return the user visible class name for homomorphism items
	 */
	public static String getItemClassName(){
		return "Tree Homomorphism";
	}
	
	/**
	 * Homomorphism stored in this item.
	 */
	private EasyHom homomorphism;
	
	/**
	 * User entered string description of the homomorphism in this item.
	 */
	private String homomorphismString;
	
	/**
	 * Creates a new homomorphism item with an empty homomorphism.
	 * @param name name of this homomorphism item
	 * @param project project this item belongs to
	 */
	public HomomorphismItem(String name, Project project) {
		super(name, project);
		this.homomorphism = new EasyHom();
	}

	/**
	 * Returns the homomorphism stored in this item.
	 * @return the homomorphism stored in this item
	 */
	public EasyHom getHomomorphism(){
		return this.homomorphism;
	}
	
	/**
	 * Returns the user entered string description of the homomorphism in this item.
	 * @return the user entered string description of the homomorphism in this item
	 */
	public String getHomomorphismString(){
		return this.homomorphismString;
	}
	
	/**
	 * Updates the homomorphism stored in this item.
	 * @param homomorphism the new homomorphism to be stored in this item
	 * @param homomorphismString the user entered string description of the new homomorphism
	 */
	public void setHomomorphism(EasyHom homomorphism, String homomorphismString){
		assert(homomorphism != null);
		assert(homomorphismString != null);
		this.homomorphism = homomorphism;
		this.homomorphismString = homomorphismString;
		super.fireItemContentSet();
	}
	
	@Override
	public Editor getEditor() {
		return new HomomorphismEditor(this);
	}
	
	@Override
	public void toXML(Element parentElement) {
		if (this.homomorphismString == null) return;
		parentElement.setTextContent(this.homomorphismString);
	}

}
