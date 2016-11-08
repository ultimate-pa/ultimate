/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.partialQuantifierElimination;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.NonTheorySymbol;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

/**
 * Partition set of terms into equivalence classes.
 * We call two terms connected if both share a common NonTheorySymbols.
 * we define two terms to be equivalent (resp. this partition) if they
 * are in the transitive closure of the connection relation.
 */
public class ConnectionPartition {
	Map<NonTheorySymbol<?>, Set<Term>> mSymbol2Terms = new HashMap<NonTheorySymbol<?>, Set<Term>>();
	UnionFind<NonTheorySymbol<?>> unionFind = new UnionFind<NonTheorySymbol<?>>();
	List<Term> mTermWithoutTvs = new ArrayList<Term>();
	
	public ConnectionPartition(final Collection<Term> parameters) {
		for (final Term term : parameters) {
			addTerm(term);
		}
	}

	private void addTerm(final Term term) {
		final Set<NonTheorySymbol<?>> symbols = NonTheorySymbol.extractNonTheorySymbols(term);
		if (symbols.isEmpty()) {
			mTermWithoutTvs.add(term);
			return;
		}
		NonTheorySymbol<?> last = null;
		for (final NonTheorySymbol<?> symbol : symbols) {
			add(term, symbol);
			if (unionFind.find(symbol) == null) {
				unionFind.makeEquivalenceClass(symbol);
			}
			if (last != null) {
				if (unionFind.find(last).equals(unionFind.find(symbol))) {
					// do nothing
					// already in same equivalence class
				} else {
					unionFind.union(symbol, last);
				}
			}
			last = symbol;
		}
	}
	
	private void add(final Term term, final NonTheorySymbol<?> symbol) {
		Set<Term> terms = mSymbol2Terms.get(symbol);
		if (terms == null) {
			terms = new HashSet<Term>();
			mSymbol2Terms.put(symbol, terms);
		}
		terms.add(term);
	}
	
	Iterable<Set<Term>> getConnectedVariables() {
		return new Iterable<Set<Term>>() {
			
			@Override
			public Iterator<Set<Term>> iterator() {

				return new Iterator<Set<Term>>() {
					private final Iterator<NonTheorySymbol<?>> mIt = unionFind.getAllRepresentatives().iterator();;

					@Override
					public boolean hasNext() {
						return mIt.hasNext();
					}

					@Override
					public Set<Term> next() {
						final Set<NonTheorySymbol<?>> eqMembers = unionFind.getEquivalenceClassMembers(mIt.next());
						return getTermsOfConnectedVariables(eqMembers);
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
					
				};
			}
		};
	}
	
	Set<Term> getTermsOfConnectedVariables(final Set<NonTheorySymbol<?>> eqMembers) {
		final Set<Term> result = new HashSet<Term>();
		for (final NonTheorySymbol<?> symbol : eqMembers) {
			result.addAll(mSymbol2Terms.get(symbol));
		}
		return result;
	}
	
	List<Term> getTermsWithOutTvs() {
		return mTermWithoutTvs;
	}
	
}
