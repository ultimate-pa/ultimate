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
package de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal;

import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.special.Cons;
import de.uni_muenster.cs.sev.lethal.symbol.special.HedgeSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.special.Nil;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.tree.standard.StdTree;

import java.util.LinkedList;
import java.util.WeakHashMap;

/**
 * Creates and caches the transformed Tree<UnrankedSymbol>.
 *
 * @author Anton, Maria
 */
public final class TreeCache {

	private static final WeakHashMap<Tree<? extends UnrankedSymbol>, Tree<? extends RankedSymbol>> treeCache = new WeakHashMap<Tree<? extends UnrankedSymbol>, Tree<? extends RankedSymbol>>();

	private TreeCache() {
		super();
	}

	/**
	 * Checks the cache for the transformed tree, generates it if needed.
	 * Returns the transformed tree.
	 *
	 * @param hedge the tree to be transformed
	 * @param <G_Symbol>   type of the symbol used the tree
	 * @return the transformed tree
	 */
	@SuppressWarnings("unchecked")
	public static <G_Symbol extends UnrankedSymbol> Tree<HedgeSymbol<G_Symbol>> getTree(
			final Tree<G_Symbol> hedge) {
		final Tree<HedgeSymbol<G_Symbol>> ret;
		if (treeCache.containsKey(hedge)) {
			ret = (Tree<HedgeSymbol<G_Symbol>>) treeCache.get(hedge);
		} else {
			ret = transformHedge(hedge);
			treeCache.put(hedge, ret);
		}
		return ret;
	}

	/**
	 * Checks the cache for the hedge, generates it if needed. Returns the
	 * transformed hedge.
	 *
	 * @param tree the tree to be transformed
	 * @param <G_Symbol>  type of the symbol used the tree
	 * @return the hedge
	 */
	@SuppressWarnings("unchecked")
	public static <G_Symbol extends UnrankedSymbol> Tree<G_Symbol> getHedge(
			final Tree<HedgeSymbol<G_Symbol>> tree) {
		if (treeCache.containsValue(tree)) {
			for (final Tree<? extends UnrankedSymbol> t : treeCache.keySet()) {
				if (treeCache.get(t).equals(tree)) {
					return (Tree<G_Symbol>) t;
				}
			}
		} else {
			final Tree<G_Symbol> ret = transformTree(tree);
			if (ret != null) {
				treeCache.put(ret, tree);
				return ret;
			}
		}
		return null;
	}

	/**
	 * Transforms a given tree into a tree with a structure needed for the
	 * hedge automaton.
	 *
	 * @param hedge the tree to be transformed
	 * @param <G_Symbol>   type of the symbol used the tree
	 * @return the transformed tree
	 */
	private static <G_Symbol extends UnrankedSymbol> Tree<HedgeSymbol<G_Symbol>> transformHedge(
			final Tree<G_Symbol> hedge) {
		final Tree<HedgeSymbol<G_Symbol>> nilTree = new StdTree<HedgeSymbol<G_Symbol>>(
				new HedgeSymbol<G_Symbol>(Nil.getNil()),
				new LinkedList<StdTree<HedgeSymbol<G_Symbol>>>());

		if (hedge.getSubTrees().isEmpty()) {
			final LinkedList<Tree<HedgeSymbol<G_Symbol>>> tmp = new LinkedList<Tree<HedgeSymbol<G_Symbol>>>();
			tmp.add(nilTree);
			// use tree factory
			return new StdTree<HedgeSymbol<G_Symbol>>(new HedgeSymbol<G_Symbol>(hedge
					.getSymbol()), tmp);
		}
		Tree<HedgeSymbol<G_Symbol>> leftSubTree = nilTree;
		LinkedList<Tree<HedgeSymbol<G_Symbol>>> subTree;
		for (final Tree<G_Symbol> h : hedge.getSubTrees()) {
			subTree = new LinkedList<Tree<HedgeSymbol<G_Symbol>>>();
			subTree.add(leftSubTree);
			subTree.add(transformHedge(h));
			leftSubTree = new StdTree<HedgeSymbol<G_Symbol>>(new HedgeSymbol<G_Symbol>(Cons
					.getCons()), subTree);
		}
		// the head element contains the hedge symbol
		subTree = new LinkedList<Tree<HedgeSymbol<G_Symbol>>>();
		subTree.add(leftSubTree);
		final HedgeSymbol<G_Symbol> newsym = new HedgeSymbol<G_Symbol>(hedge.getSymbol());

		return new StdTree<HedgeSymbol<G_Symbol>>(newsym, subTree);
	}

	/**
	 * Transforms a given tree into a hedge.
	 *
	 * @param tree the tree to be transformed
	 * @param <G_Symbol>  type of the symbol used the tree
	 * @return the transformed tree
	 */
	private static <G_Symbol extends UnrankedSymbol> Tree<G_Symbol> transformTree(
			final Tree<HedgeSymbol<G_Symbol>> tree) {
		if (tree != null) {
			if ((tree.getSubTrees().get(0).getSymbol().isNil())
					&& (tree.getSubTrees().size()) == 1)
				return new StdTree<G_Symbol>(tree.getSymbol().getOriginal(),
						new LinkedList<Tree<G_Symbol>>());
			if ((tree.getSubTrees().size() == 1)
					&& (tree.getSubTrees().get(0).getSymbol().isCons())) {
				Tree<HedgeSymbol<G_Symbol>> subTree = tree.getSubTrees().get(0);
				final LinkedList<Tree<G_Symbol>> subs = new LinkedList<Tree<G_Symbol>>();
				while (subTree.getSymbol().isCons()) {
					final Tree<G_Symbol> tmp = transformTree(subTree.getSubTrees().get(1));
					if (tmp == null)
						return null;
					subs.add(0, tmp);
					subTree = subTree.getSubTrees().get(0);
				}
				if (subTree.getSymbol().isNil()) {
					return new StdTree<G_Symbol>(tree.getSymbol().getOriginal(), subs);
				}
			}
		}
		return null;
	}

}
