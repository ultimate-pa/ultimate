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
/**
 * 
 */
package de.uni_muenster.cs.sev.lethal.treeautomata.common;


/**
 * Represents an epsilon rule of a finite tree automaton, which is of the form
 * q -> r where q and r are states. <br> 
 * q is called <em>source state</em>, r is called <em>destination state</em>. <br>
 * Epsilon rules help to define some automata easier. They can be eliminated.
 * 
 * @param <Q> state type occurring in rule
 * 
 * @author Dorothea, Irene, Martin
 */
public interface FTAEpsRule<Q> {

	/**
	 * Returns the source state of the left side of this rule.
	 * 
	 * @return the source state of this rule
	 */
	Q getSrcState();

	/**
	 * Returns the destination state of the right side of this rule.
	 * 
	 * @return the destination state of this rule
	 */
	Q getDestState();
}
