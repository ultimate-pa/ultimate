package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.UnionFind;

/**
 * Partition set of terms into equivalence classes. 
 * We call two terms connected if both share a common NonTheorySymbols.
 * we define two terms to be equivalent (resp. this partition) if they
 * are in the transitive closure of the connection relation.
 */
public class ConnectionPartition {
	Map<NonTheorySymbol<?>, Set<Term>> m_Symbol2Terms = new HashMap<NonTheorySymbol<?>, Set<Term>>();
	UnionFind<NonTheorySymbol<?>> unionFind = new UnionFind<NonTheorySymbol<?>>();
	List<Term> m_TermWithoutTvs = new ArrayList<Term>();
	
	public ConnectionPartition(Collection<Term> parameters) {
		for (Term term : parameters) {
			addTerm(term);
		}
	}

	private void addTerm(Term term) {
		Set<NonTheorySymbol<?>> symbols = NonTheorySymbol.extractNonTheorySymbols(term);
		if (symbols.size() == 0) {
			m_TermWithoutTvs.add(term);
			return;
		}
		NonTheorySymbol<?> last = null;
		for (NonTheorySymbol<?> symbol : symbols) {
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
	
	private void add(Term term, NonTheorySymbol<?> symbol) {
		Set<Term> terms = m_Symbol2Terms.get(symbol);
		if (terms == null) {
			terms = new HashSet<Term>();
			m_Symbol2Terms.put(symbol, terms);
		}
		terms.add(term);
	}
	
	Iterable<Set<Term>> getConnectedVariables() {
		return new Iterable<Set<Term>>() {
			
			@Override
			public Iterator<Set<Term>> iterator() {

				return new Iterator<Set<Term>>() {
					private Iterator<NonTheorySymbol<?>> m_It;

					{
						m_It = unionFind.getAllRepresentatives().iterator();
					}

					@Override
					public boolean hasNext() {
						return m_It.hasNext();
					}

					@Override
					public Set<Term> next() {
						Set<NonTheorySymbol<?>> eqMembers = unionFind.getEquivalenceClassMembers(m_It.next());
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
	
	Set<Term> getTermsOfConnectedVariables(Set<NonTheorySymbol<?>> eqMembers) {
		Set<Term> result = new HashSet<Term>();
		for (NonTheorySymbol<?> symbol : eqMembers) {
			result.addAll(m_Symbol2Terms.get(symbol));
		}
		return result;
	}
	
	List<Term> getTermsWithOutTvs() {
		return m_TermWithoutTvs;
	}
	
}