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

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;


/**
 * A rule set implementation which stores the finite tree automata rules 
 * in a more simple (but maybe also slower) way. 
 * 
 * @param <Q> state type used in the rules
 * @param <F> symbol type used in the rules
 * @param <R> rules type
 * 
 * @see FTARuleSet
 * 
 * @author Dorothea, Irene, Martin
 */
public class SimpleFTARuleSet<F extends RankedSymbol, Q extends State,R extends FTARule<F,Q>> extends FTARuleSet<F,Q,R> {

	/** The underlying structure is just a set of rules. */
	private Set<R> rules;

	/** Map that maps each symbol to the set of rules that use this symbol. */	
	private Map<F, Set<R>> symbolRules = new HashMap<F,Set<R>>();


	/**
	 * Constructs a new SimpleFTARuleSet by a given collection of rules.
	 * @param newRules rules that shall form the set of rules
	 */
	public SimpleFTARuleSet(Collection<? extends R> newRules) {
		rules = new HashSet<R>();
		for (R r: newRules)
			add(r);
	}

	/**
	 * Constructs an empty SimpleFTARuleSet.
	 */
	public SimpleFTARuleSet() {
		rules = new HashSet<R>();
	}

	/**
	 * @see java.util.Set#add(java.lang.Object)
	 */
	@Override
	public boolean add(R e) {
		if (symbolRules.containsKey(e.getSymbol()))
			symbolRules.get(e.getSymbol()).add(e);
		return this.rules.add(e);
	}

	/** 
	 * @see java.util.Set#clear()
	 */
	@Override
	public void clear() {
		this.rules.clear();
	}

	/**
	 * @see java.util.Set#contains(java.lang.Object)
	 */
	@Override
	public boolean contains(Object o) {
		return this.rules.contains(o);
	}

	/**
	 * @see java.util.Set#containsAll(java.util.Collection)
	 */
	@Override
	public boolean containsAll(Collection<?> c) {
		return this.rules.containsAll(c);
	}

	/**
	 * @see java.util.Set#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object o) {
		return o.getClass() == this.getClass()
		&& this.rules.equals(o);
	}

	/**
	 * @see java.util.Set#hashCode()
	 */
	@Override
	public int hashCode() {
		return this.rules.hashCode();
	}

	/**
	 * @see java.util.Set#isEmpty()
	 */
	@Override
	public boolean isEmpty() {
		return this.rules.isEmpty();
	}

	/**
	 * @see java.util.Set#iterator()
	 */
	@Override
	public Iterator<R> iterator() {
		return this.rules.iterator();
	}

	/**
	 * @see java.util.Set#remove(java.lang.Object)
	 */
	@Override
	public boolean remove(Object o) {
		if (!(o instanceof FTARule<?,?>))
			return false;
		else {
			FTARule<?,?> r = (FTARule<?,?>)o;
			Set<R> fRules = symbolRules.get(r.getSymbol());
			fRules.remove(r);
			return this.rules.remove(o);
		}

	}

	/**
	 * @see java.util.Set#removeAll(java.util.Collection)
	 */
	@Override
	public boolean removeAll(Collection<?> c) {
		boolean ret = false;
		for (Object o: c)
			ret = ret || remove(o);
		return ret;
	}

	/**
	 * @see java.util.Set#retainAll(java.util.Collection)
	 */
	@Override
	public boolean retainAll(Collection<?> c) {
		return this.rules.retainAll(c);
	}

	/**
	 * @see java.util.Set#size()
	 */
	@Override
	public int size() {
		return this.rules.size();
	}

	/**
	 * @see java.util.Set#toArray()
	 */
	@Override
	public Object[] toArray() {
		return this.rules.toArray();
	}

	/**
	 * @see java.util.Set#toArray(Object[])
	 */
	@Override
	public <T> T[] toArray(T[] a) {
		return this.rules.toArray(a);
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARuleSet#getSymbolRules
	 */
	@Override
	public Set<R> getSymbolRules(F f) {
		Set<R> ret;
		if (!symbolRules.containsKey(f)) {
			ret = new HashSet<R>();
			for (R r: rules) {
				if (r.getSymbol().equals(f))
					ret.add(r);
			}
			symbolRules.put(f, ret);
		}
		return symbolRules.get(f);
	}

	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		StringBuffer text = new StringBuffer();
		for(R rule: this){
			text.append(rule.toString()).append("\n");
		}
		return text.toString();
	}
}
