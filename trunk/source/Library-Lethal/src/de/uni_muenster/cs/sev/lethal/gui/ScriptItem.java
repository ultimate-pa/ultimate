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
 * GUI item encapsulating a script.
 * @author Philipp
 *
 */
public class ScriptItem extends Item {
	/**
	 * User visible class name of this item class.
   * @return User visible class name of this item class
   */
	public static String getItemClassName(){
		return "Script";
	}
	
	/**
	 * Reads the script stored in an XML element.
	 * @param parentElement XML element to read from
	 * @param project project this item will belong to
	 * @return the loaded script item
	 */
	public static ScriptItem fromXML(Element parentElement, Project project){
		String script = parentElement.getTextContent().trim();
		String name = parentElement.getAttribute("name");
		ScriptItem item = new ScriptItem(name,project);
		item.script = script;
		return item;
	}
	
	/**
	 * The script stored in this item.
	 */
	String script;

	/**
	 * Creates a new empty script item. 
	 * @param name name of the item
	 * @param project project this item belongs to
	 */
	public ScriptItem(String name, Project project) {
		super(name, project);
		this.script = "";
	}

	/**
	 * Returns the script stored in this item.
	 * @return the script stored in this item
	 */
	public String getScript() {
		return script;
	}

	/**
	 * Updates the script stored in this item.
	 * @param script the new script
	 */
	public void setScript(String script) {
		if (!this.script.equals(script)){
			this.script = script;
			super.fireItemContentSet();
		}
	}

	@Override
	public Editor getEditor() {
		return new ScriptEditor(this);
	}
	
	@Override
	public void toXML(Element parentElement) {
		parentElement.setTextContent(script);
	}

}
