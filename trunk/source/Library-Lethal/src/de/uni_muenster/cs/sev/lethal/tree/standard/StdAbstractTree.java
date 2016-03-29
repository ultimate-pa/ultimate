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
package de.uni_muenster.cs.sev.lethal.tree.standard;

import de.uni_muenster.cs.sev.lethal.symbol.common.Symbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;

/**
 * Base class of the standard tree implementation which provides some common functionality.
 * 
 * @param <S> tree node symbol type
 * 
 * @author Anton, Dorothea, Irene, Maria, Martin, Philipp, Sezar
 */
public abstract class StdAbstractTree<S extends Symbol> implements Tree<S> {

	/**
	 * Hash code of the tree. Can be precalculated because the tree never can be changed!
	 */
	private int hash = -1;


	/**
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode(){
		if (this.hash < 0 ) this.hash = calcHashCode();
		return this.hash;
	}


	/**
	 * Calculates the hash code once, to re-use later.
	 *
	 * @return hash code - can be used later since tree is not changed
	 * after creation
	 */
	protected int calcHashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
		+ ((this.getSubTrees() == null) ? 0 : this.getSubTrees().hashCode());
		result = prime * result
		+ ((this.getSymbol() == null) ? 0 : this.getSymbol().hashCode());
		return result;
	}


	/**
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@SuppressWarnings("unchecked")
	@Override
	public boolean equals(Object t) {
		if (t == null) return false;
		if (!(t instanceof Tree)) return false;
		Tree tree = (Tree)t;
		// Slow, recursive compare
		return (this.getSymbol().equals(tree.getSymbol()) && this.getSubTrees().equals(tree.getSubTrees()));
	}


	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		if (this.getSubTrees().size() == 0) {
			return this.getSymbol().toString();
		} else {
			StringBuffer ret = new StringBuffer(this.getSymbol().toString());
			ret.append("(");
			for (Tree<S> node : this.getSubTrees())
				ret.append(node.toString()).append(",");
			ret.replace(ret.length() - 1, ret.length(), ")");
			return ret.toString();
		}
	}

}
