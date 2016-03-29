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

import de.uni_muenster.cs.sev.lethal.hedgeautomaton.HedgeAutomaton;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.special.Cons;
import de.uni_muenster.cs.sev.lethal.symbol.special.HedgeSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.special.Nil;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;

import java.util.WeakHashMap;

/**
 * This class implements a symbol cache. It is used to cache packed symbols for the
 * hedge automaton. The needed symbols are generated if needed and returned if
 * wanted.
 *
 * @author Anton, Maria
 */
public final class HedgeSymbolCache {
	private static final WeakHashMap<UnrankedSymbol, HedgeSymbol<?>> symbolCache = new WeakHashMap<UnrankedSymbol, HedgeSymbol<?>>();
	private static final WeakHashMap<HedgeAutomaton<? extends UnrankedSymbol, ? extends State>, HedgeSymbol<?>> nilCache1 = new WeakHashMap<HedgeAutomaton<? extends UnrankedSymbol, ? extends State>, HedgeSymbol<?>>();
	private static final WeakHashMap<Tree<? extends UnrankedSymbol>, HedgeSymbol<?>> nilCache2 = new WeakHashMap<Tree<? extends UnrankedSymbol>, HedgeSymbol<?>>();
	private static final WeakHashMap<HedgeAutomaton<? extends UnrankedSymbol, ? extends State>, HedgeSymbol<?>> consCache1 = new WeakHashMap<HedgeAutomaton<? extends UnrankedSymbol, ? extends State>, HedgeSymbol<?>>();
	private static final WeakHashMap<Tree<? extends UnrankedSymbol>, HedgeSymbol<?>> consCache2 = new WeakHashMap<Tree<? extends UnrankedSymbol>, HedgeSymbol<?>>();

	private HedgeSymbolCache() {
		super();
	}

	/**
	 * Checks the cache for the transformed symbol, generates it if needed.
	 * Returns the transformed symbol.
	 *
	 * @param symbol the symbol to be transformed
	 * @param <G_Symbol>    type of the symbol
	 * @return the transformed symbol
	 */
	@SuppressWarnings("unchecked")
	public static <G_Symbol extends UnrankedSymbol> HedgeSymbol<G_Symbol> getSymbol(
			final G_Symbol symbol) {
		final HedgeSymbol<G_Symbol> ret;
		if (symbolCache.containsKey(symbol)) {
			ret = (HedgeSymbol<G_Symbol>) symbolCache.get(symbol);
		} else {
			ret = new HedgeSymbol<G_Symbol>(symbol);
			symbolCache.put(symbol, ret);
		}
		return ret;
	}

	/**
	 * Checks the cache for the transformed nil symbol, generates it if needed.
	 * Returns the transformed symbol.
	 *
	 * @param ha	the automaton the nil is needed in
	 * @param <G_State> type of the states used in the given hedge automaton
	 * @param <G_Symbol> type of the symbol
	 * @return the transformed symbol
	 */
	@SuppressWarnings("unchecked")
	public static <G_Symbol extends UnrankedSymbol, G_State extends State> HedgeSymbol<G_Symbol> getNilSymbol(
			final HedgeAutomaton<G_Symbol, G_State> ha) {
		final HedgeSymbol<G_Symbol> ret;
		if (nilCache1.containsKey(ha)) {
			// this cast is safe, because the stored
			// hedge symbol has always the same symbol type as the
			// hedge automaton used as key
			ret = (HedgeSymbol<G_Symbol>) nilCache1.get(ha);
		} else {
			ret = new HedgeSymbol<G_Symbol>(Nil.getNil());
			nilCache1.put(ha, ret);
		}
		return ret;
	}

	/**
	 * Checks the cache for the transformed nil symbol, generates it if needed.
	 * Returns the transformed symbol
	 *
	 * @param tree the tree the nil is needed in
	 * @param <G_Symbol>  type of the symbol
	 * @return the transformed symbol
	 */
	@SuppressWarnings("unchecked")
	public static <G_Symbol extends UnrankedSymbol> HedgeSymbol<G_Symbol> getNilSymbol(
			final Tree<G_Symbol> tree) {
		final HedgeSymbol<G_Symbol> ret;
		if (nilCache2.containsKey(tree)) {
			// this cast is safe, because the stored
			// hedge symbol has always the same symbol type as the
			// tree used as key
			ret = (HedgeSymbol<G_Symbol>) nilCache2.get(tree);
		} else {
			ret = new HedgeSymbol<G_Symbol>(Nil.getNil());
			nilCache2.put(tree, ret);
		}
		return ret;
	}

	/**
	 * Checks the cache for the transformed cons symbol, generates it if needed.
	 * Returns the transformed symbol.
	 *
	 * @param ha	the automaton the cons is needed in
	 * @param <G_State> type of the states used in the given hedge automaton
	 * @param <G_Symbol> type of the symbol
	 * @return the transformed symbol
	 */
	@SuppressWarnings("unchecked")
	public static <G_Symbol extends UnrankedSymbol, G_State extends State> HedgeSymbol<G_Symbol> getConsSymbol(
			final HedgeAutomaton<G_Symbol, G_State> ha) {
		final HedgeSymbol<G_Symbol> ret;
		if (consCache1.containsKey(ha)) {
			// this cast is safe, because the stored
			// hedge symbol has always the same symbol type as the
			// hedge automaton used as key
			ret = (HedgeSymbol<G_Symbol>) consCache1.get(ha);
		} else {
			ret = new HedgeSymbol<G_Symbol>(Cons.getCons());
			consCache1.put(ha, ret);
		}
		return ret;
	}

	/**
	 * Checks the cache for the transformed nil symbol, generates it if needed.
	 * Returns the transformed symbol.
	 *
	 * @param tree the tree the nil is needed in
	 * @param <G_Symbol>  type of the symbol
	 * @return the transformed symbol
	 */
	@SuppressWarnings("unchecked")
	public static <G_Symbol extends UnrankedSymbol> HedgeSymbol<G_Symbol> getConsSymbol(
			final Tree<G_Symbol> tree) {
		final HedgeSymbol<G_Symbol> ret;
		if (consCache2.containsKey(tree)) {
			// this cast is safe, because the stored
			// hedge symbol has always the same symbol type as the
			// tree used as key
			ret = (HedgeSymbol<G_Symbol>) consCache2.get(tree);
		} else {
			ret = new HedgeSymbol<G_Symbol>(Nil.getNil());
			consCache2.put(tree, ret);
		}
		return ret;
	}
}
