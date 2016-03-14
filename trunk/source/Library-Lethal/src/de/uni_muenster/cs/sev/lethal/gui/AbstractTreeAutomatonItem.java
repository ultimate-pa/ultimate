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

/**
 * Abstract superclass for FTA and hedge automaton items.
 * @author Philipp
 */
public abstract class AbstractTreeAutomatonItem extends Item {
	
	
	/** Rules parser */
	public static final int INPUT_MODE_RULES = 0;	
	/** Grammar parser */
	public static final int INPUT_MODE_GRAMMAR = 1;
	
	protected String automatonString;
	protected int inputMode;
	
	protected AbstractTreeAutomatonItem(String name, Project project) {
		super(name, project);
	}
	
	/**
	 * Returns the input mode used for the tree automaton represented by this item.<br>
	 * Supported values are INPUT_MODE_RULES and INPUT_MODE_GRAMMAR.
	 * @return the input mode used for the tree automaton represented by this item.
	 */
	public int getInputMode(){
		return inputMode;
	}

}
