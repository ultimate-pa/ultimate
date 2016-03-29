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
package de.uni_muenster.cs.sev.lethal.factories;

import java.lang.ref.WeakReference;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;

import de.uni_muenster.cs.sev.lethal.symbol.common.Symbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.tree.standard.StdTree;
import de.uni_muenster.cs.sev.lethal.utils.Pair;

/**
 * Factory for creating trees.
 * It uses a cache to re-use an existing tree if an equivalent tree shall be created.
 * 
 * @author Philipp
 */
public class StdTreeFactory extends TreeFactory {
		
	private HashMap<Object, WeakReference<StdFactoryTree<? extends Symbol>>> cache = new HashMap<Object, WeakReference<StdFactoryTree<? extends Symbol>>>(); 
	
	/**
	 * Creates a Tree with no subtrees (that means a leaf) from a given symbol.<br>
	 * Trees are cached and the old tree is returned if there already is a leaf tree with the same symbol.
	 * @param <S> type of the symbol
	 * @param rootSymbol symbol of the tree root.
	 * @return a tree with no subtrees and the given symbol.
	 */
	@Override
	public <S extends Symbol> Tree<S> makeTreeFromSymbol(S rootSymbol){
		return makeTreeFromSymbol(rootSymbol, Collections.<Tree<S>>emptyList());
	}
	
	/**
	 * Creates a new Tree with given subtrees. <br>
	 * Trees are cached and the old tree is returned if there already is a tree with the same symbol and subtrees.
	 * @param <S> type of the symbol
	 * @param rootSymbol symbol of the tree root
	 * @param subtrees subtrees of the tree
	 * @return the created tree
	 */
	@Override
	@SuppressWarnings("unchecked")
	public <S extends Symbol> Tree<S> makeTreeFromSymbol(S rootSymbol, List<? extends Tree<S>> subtrees){
		Pair<S,List<? extends Tree<S>>> key = new Pair<S,List<? extends Tree<S>>>(rootSymbol,subtrees);
		StdFactoryTree<? extends Symbol> tree = null;
		WeakReference<StdFactoryTree<? extends Symbol>> wref = this.cache.get(key);
		if (wref != null) tree = wref.get();
		
		if (tree == null) {
			tree = new StdFactoryTree<S>(rootSymbol, subtrees);
			cache.put(key, new WeakReference<StdFactoryTree<? extends Symbol>>(tree));
		}
		/*
		 * If a tree is found, its symbol type is determined by the key and thus by the
		 * inferred symbol type. 
		 * Otherwise, a new tree of the inferred symbol type is created.
		 * In both cases, the variable tree holds a StdFactoryTree of the inferred symbol
		 * type, so the following cast is safe: 
		 */
		return (StdFactoryTree<S>)tree;
	}
	
	
	/**
	 * Private subclass for trees created by this factory.<br>
	 * Uses fast reference compare because equivalent trees are returned from cache.
	 *
	 * @param <S> type of the tree symbol
	 */
	private class StdFactoryTree<S extends Symbol> extends StdTree<S>{
		
		/**Used tree factory.*/
		
		protected TreeFactory tf;
		/**
		 * Constructs a new tree.
		 * 
		 * @see StdTree
		 * @param symbol root symbol of the tree
		 * @param subtrees subtrees of the tree
		 */
		public StdFactoryTree(S symbol, List<? extends Tree<S>> subtrees) {
			super(symbol, subtrees);
			tf = StdTreeFactory.this;
		}
		
		
		/**
		 * @see de.uni_muenster.cs.sev.lethal.tree.standard.StdAbstractTree#equals(java.lang.Object)
		 */
		@Override
		public boolean equals(Object t){ //Optimized compare for trees that are created with this factory.
			if (t == null) return false;
			if (!(t instanceof Tree<?>)) return false;
			if (!(t instanceof StdFactoryTree<?>)) 
				return super.equals(t);
			else {
				StdFactoryTree<?> sftt = (StdFactoryTree<?>)t;
				if (sftt.tf.equals(this.tf))
					return t == this;
				else
					return super.equals(t);
			}
		}
		
	}
	
}
