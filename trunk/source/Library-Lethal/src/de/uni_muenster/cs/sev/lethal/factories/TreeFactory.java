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

import java.util.HashMap;
import java.util.List;

import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.Symbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.special.HedgeSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.standard.StdNamedRankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.standard.StdNamedUnrankedSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;

/**
 * Factory for creating trees.<br>
 * It uses a cache to re-use an existing tree if an equivalent tree shall be created.
 * @author Philipp
 */
public abstract class TreeFactory {

	private static TreeFactory genericTreeFactory = null;

	private static HashMap<Class<? extends Symbol>, NamedSymbolTreeFactory<? extends Symbol>> namedSymbolTreeFactories = new HashMap<Class<? extends Symbol>, NamedSymbolTreeFactory<? extends Symbol>>(); 

	static {
		namedSymbolTreeFactories.put(UnrankedSymbol.class, new NamedSymbolTreeFactory<UnrankedSymbol>(UnrankedSymbol.class){
			@Override
			protected <T> UnrankedSymbol makeSymbol(T name, List<? extends Tree<UnrankedSymbol>> subtrees) {
				return new StdNamedUnrankedSymbol<T>(name);
			}
		});
		namedSymbolTreeFactories.put(StdNamedUnrankedSymbol.class, new NamedSymbolTreeFactory<StdNamedUnrankedSymbol>(StdNamedUnrankedSymbol.class){
			@SuppressWarnings("unchecked")
			@Override
			protected <T> StdNamedUnrankedSymbol<T> makeSymbol(T name, List<? extends Tree<StdNamedUnrankedSymbol>> subtrees) {
				return new StdNamedUnrankedSymbol<T>(name);
			}
		});
		namedSymbolTreeFactories.put(RankedSymbol.class, new NamedSymbolTreeFactory<RankedSymbol>(RankedSymbol.class){
			@Override
			protected <T> RankedSymbol makeSymbol(T name, List<? extends Tree<RankedSymbol>> subtrees) {
				return new StdNamedRankedSymbol<T>(name, subtrees.size());
			}
		});
		namedSymbolTreeFactories.put(StdNamedRankedSymbol.class, new NamedSymbolTreeFactory<StdNamedRankedSymbol>(StdNamedRankedSymbol.class){
			@SuppressWarnings("unchecked")
			@Override
			protected <T> StdNamedRankedSymbol<T> makeSymbol(T name, List<? extends Tree<StdNamedRankedSymbol>> subtrees) {
				return new StdNamedRankedSymbol<T>(name, subtrees.size());
			}
		});
		namedSymbolTreeFactories.put(HedgeSymbol.class, new NamedSymbolTreeFactory<StdNamedRankedSymbol>(StdNamedRankedSymbol.class){
			@SuppressWarnings("unchecked")
			@Override
			protected <T> StdNamedRankedSymbol<T> makeSymbol(T name, List<? extends Tree<StdNamedRankedSymbol>> subtrees) {
				return new StdNamedRankedSymbol<T>(name, subtrees.size());
			}
		});
	}

	/**
	 * Initially sets a non-standard tree factory.
	 * @param factory the tree factory sill use
	 */
	public static void init(TreeFactory factory){
		assert(genericTreeFactory == null);
		genericTreeFactory = factory;
	}
	
	/**
	 * Returns a tree factory instance that can create trees from a root symbol and subtrees.
	 * @return a tree factory instance that can create trees from a root symbol and subtrees
	 */
	public static TreeFactory getTreeFactory(){
		if (genericTreeFactory == null) genericTreeFactory = new StdTreeFactory();
		return genericTreeFactory;
	}

	/**
	 * Returns a NamedSymbolTreeFactory instance that can create trees with named symbol sub-types
	 * from a symbol name and subtrees. The symbol creation is handled by the NamedSymbolTreeFactory.
	 * Currently creation of UnrankedSymbol and RankedSymbol trees is supported.The returned objects
	 * are instances of StdNamedUnrankedSymbol and StdNamedRankedSymbol respectively.
	 * @param <S> class of the symbol to create (inferred automatically by compiler)
	 * @param symClass class of the symbol to create
	 * @return a symbol factory for the given symbol type, or NULL if the type is not supported.
	 */
	@SuppressWarnings("unchecked")
	public static <S extends Symbol> NamedSymbolTreeFactory<S> getTreeFactory(Class<? extends S> symClass) {
		/* 
		 * the following cast is safe because the symbol type associated to the tree factory
		 * is compatible to the type of the key, see {@link #putTreeFactory}
		 */
		return (NamedSymbolTreeFactory<S>)namedSymbolTreeFactories.get(symClass);
	}

	/**
	 * Registers a new NamedSymbolTreeFactory for a Symbol class. 
	 * 
	 * @param <S> class of the symbol to create (inferred automatically by compiler)
	 * @param symClass class of the symbol to create
	 * @param factory the NamedSymbolTreeFactory to create
	 */
	public static <S extends Symbol> void putTreeFactory(Class<? extends S> symClass, NamedSymbolTreeFactory<S> factory){
		namedSymbolTreeFactories.put(symClass, factory);
	}

	/**
	 * Creates a Tree with no subtrees (Leaf) from a given symbol.
	 * @param <S> type of the symbol
	 * @param rootSymbol symbol of the tree root
	 * @return a tree with no subtrees and the given symbol
	 */
	public abstract <S extends Symbol> Tree<S> makeTreeFromSymbol(S rootSymbol);

	/**
	 * Creates a new Tree with given subtrees.
	 * @param <S> type of the symbol
	 * @param rootSymbol symbol of the tree root
	 * @param subtrees subtrees of the tree
	 * @return the created tree
	 */
	public abstract <S extends Symbol> Tree<S> makeTreeFromSymbol(S rootSymbol, List<? extends Tree<S>> subtrees);

}
