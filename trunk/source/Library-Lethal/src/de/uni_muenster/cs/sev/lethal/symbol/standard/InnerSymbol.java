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
package de.uni_muenster.cs.sev.lethal.symbol.standard;

import de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.Symbol;

/**
 * Wraps a symbol as inner symbol of a BiTree (that is a tree containing BiSymbols).<br>
 * In such a tree, an inner symbol can be any inner or leaf node.
 * 
 * @param <I> inner type of wrapping BiSymbol
 * @param <L> leaf type of wrapping BiSymbol
 * 
 * @author Dorothea, Irene, Martin
 * 
 * @see BiSymbol
 * @see LeafSymbol
 */
public class InnerSymbol<I extends Symbol, L> implements BiSymbol<I,L> {

	/**
	 * Wrapped symbol.
	 */
	private I symbol;


	/**
	 * Constructs a new inner symbol by some given symbol.
	 * 
	 * @param symbol symbol to be wrapped
	 */
	public InnerSymbol(I symbol) {
		if (symbol == null) throw new IllegalArgumentException("InnerSymbol(): symbol must not be null.");
		this.symbol = symbol;
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol#asInnerSymbol()
	 */
	@Override
	public I asInnerSymbol() {
		return symbol;
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol#asLeafSymbol()
	 */
	@Override
	public L asLeafSymbol() {
		return null;
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol#isInnerType()
	 */
	@Override
	public boolean isInnerType() {
		return true;
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol#isLeafType()
	 */
	@Override
	public boolean isLeafType() {
		return false;
	}


	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString(){
		return this.symbol.toString();
	}


	/**
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
		+ ((this.symbol == null) ? 0 : this.symbol.hashCode());
		return result;
	}


	/**
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		InnerSymbol<?,?> other = (InnerSymbol<?,?>) obj;
		if (this.symbol == null) {
			if (other.symbol != null)
				return false;
		} else if (!this.symbol.equals(other.symbol))
			return false;
		return true;
	}
}
