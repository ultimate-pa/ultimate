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
package de.uni_muenster.cs.sev.lethal.symbol.special;

import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;

/**
 * Special symbol to be used in transformed trees. <br>
 * Needed to contain both the user and the Nil/Cons symbols.
 *
 * @param <G_Symbol> type of the unranked symbols
 * 
 * @author Anton, Maria
 */
public class HedgeSymbol<G_Symbol extends UnrankedSymbol> implements RankedSymbol {


	private RankedSymbol i;
	private G_Symbol s;

	/**
	 * Puts the nil symbol in.
	 *
	 * @param nil the nil symbol
	 */
	public HedgeSymbol(final Nil nil) {
		super();
		assert nil != null;
		this.i = nil;
		this.s = null;
	}


	/**
	 * Puts the cons symbol in.
	 *
	 * @param cons the cons symbol
	 */
	public HedgeSymbol(final Cons cons) {
		super();
		assert cons != null;
		this.i = cons;
		this.s = null;
	}


	/**
	 * Puts a user symbol in.
	 *
	 * @param symbol the user symbol
	 */
	public HedgeSymbol(final G_Symbol symbol) {
		super();
		assert symbol != null;
		this.s = symbol;
		this.i = null;
	}


	/**
	 * Getter for the user symbol.
	 *
	 * @return the contained user symbol
	 */
	public G_Symbol getOriginal() {
		if (this.s == null) throw new IllegalAccessError("Tried to unpack a hedge symbol without packed symbol in it.");
		return this.s;
	}


	/**
	 * Checks whether this is the user symbol.
	 *
	 * @return whether this is the user symbol
	 */
	public boolean isPacked() {
		return this.i == null;
	}


	/**
	 * Checks whether this is the Nil symbol.
	 *
	 * @return whether this is the Nil symbol
	 */
	public boolean isNil() {
		return this.i == Nil.getNil();
	}


	/**
	 * Checks whether this is the Cons symbol.
	 *
	 * @return whether this is the Cons symbol
	 */
	public boolean isCons() {
		return this.i == Cons.getCons();
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol#getArity()
	 */
	@Override
	public int getArity() {
		if (this.s == null) return this.i.getArity();
		return 1;
	}


	/**
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((i == null) ? 0 : i.hashCode());
		result = prime * result + ((s == null) ? 0 : s.hashCode());
		return result;
	}


	/**
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(final Object symbol) {
		if (symbol == null) return false;
		if (symbol == this) return true;
		if (symbol instanceof HedgeSymbol<?>) {
			final HedgeSymbol<?> h_symbol = (HedgeSymbol<?>) symbol;
			if (this.isPacked())
				return (h_symbol.isPacked() && this.getOriginal().equals(h_symbol.getOriginal()));
			else
				return (!h_symbol.isPacked() && this.isNil() == h_symbol.isNil());
		} else
			return false;
	}


	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "H<" + ((this.i != null) ? this.i.toString() : this.s.toString()) + ">";
	}


}
