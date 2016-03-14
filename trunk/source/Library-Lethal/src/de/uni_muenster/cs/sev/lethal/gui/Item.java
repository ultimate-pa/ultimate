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

/**
 * Base class for all things the GUI can edit.
 * @author Philipp
 */
public abstract class Item {
	
	/**
	 * Returns the user visible name for the given item class by calling the static getItemClassName method of the item class.<br>
	 * Using getMethod seems to be the only way to do this. :(<br>
	 * There is no way to enforce the implementation of the getItemClassName methods by subclasses,
	 * so this method uses a fallback to the source class name in case getItemClassName is not (correctly) implemented.
	 * @param itemClass item class
	 * @return user visible name for the given item class
	 */
	public static String getItemClassName(Class<? extends Item> itemClass){
		try { //Ugly Ugly Java reflection crap...
			return (String)(itemClass.getMethod("getItemClassName").invoke(itemClass));
		} catch (Exception e) {
			return itemClass.getSimpleName();
		}
	}
	
	/**
	 * Name of this item.
	 */
	private String name;
	/**
	 * Project this item belongs to.
	 */
	private Project project;
	
	/**
	 * Create a new item.
	 * @param name name of the new item
	 * @param project project this item belongs to
	 */
	protected Item(String name, Project project){
		this.name = name;
		this.project = project;
	}
	
	/**
	 * Returns an editor widget for this item.
	 * @return editor widget for this item
	 */
	public abstract Editor getEditor();

	/**
	 * Returns the User visible name for this Item.
	 * @return name of this item
	 */
	public String getName(){
		return this.name;
	}
	
	/**
	 * Sets a new User visible name for this Item.
	 * @param newName User visible name for this Item.
	 */
	public void setName(String newName){
		if (!this.name.equals(newName)){
			this.name = newName;
			project.fireItemRenamed(this);
		}
	}
	
	/**
	 * Passes content set event to the project. <br> 
	 * To be called by subclasses after an item has been edited by the user and apply is pressed.
	 */
	protected void fireItemContentSet(){
		this.project.fireItemContentSet(this);
	}
	
	
	/**
	 * Returns the project, this item belongs to.
	 * @return the project, this item belongs to.
	 */
	public Project getProject(){
		return this.project;
	}
	
	/**
	 * Store the item content in a serialized form into the given XML Element.
	 * @param parentElement XML Element to serialize to.
	 */
	public abstract void toXML(Element parentElement);
	
	@Override
	public String toString(){
		return this.name;
	}
}
