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
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.UnionFind;

/**
 * Partition set of terms into equivalence classes. 
 * We call two terms connected if both share a common free variable.
 * we define two terms to be equivalent (resp. this partition) if they
 * are in the transitive closure of the connection relation.
 */
public class ConnectionPartition {
	Map<TermVariable, Set<Term>> m_Tv2Terms = new HashMap<TermVariable, Set<Term>>();
	UnionFind<TermVariable> unionFind = new UnionFind<TermVariable>();
	List<Term> m_TermWithoutTvs = new ArrayList<Term>();
	
	public ConnectionPartition(Collection<Term> parameters) {
		for (Term term : parameters) {
			addTerm(term);
		}
	}

	private void addTerm(Term term) {
		TermVariable[] tvs = term.getFreeVars();
		if (tvs.length == 0) {
			m_TermWithoutTvs.add(term);
			return;
		}
		TermVariable firstTv = tvs[0];
		add(term, firstTv);
		if (unionFind.find(firstTv) == null) {
			unionFind.makeEquivalenceClass(firstTv);
		}
		for (int i=1; i < tvs.length; i++) {
			add(term, tvs[i]);
			if (unionFind.find(tvs[i]) == null) {
				unionFind.makeEquivalenceClass(tvs[i]);					
			} 
			if (unionFind.find(firstTv).equals(unionFind.find(tvs[i]))) {
				// already in same equivalence class
			} else {
				unionFind.union(tvs[i], firstTv);
			}
		}
	}
	
	private void add(Term term, TermVariable tv) {
		Set<Term> terms = m_Tv2Terms.get(tv);
		if (terms == null) {
			terms = new HashSet<Term>();
			m_Tv2Terms.put(tv, terms);
		}
		terms.add(term);
	}
	
	Iterable<Set<TermVariable>> getConnectedVariables() {
		return new Iterable<Set<TermVariable>>() {
			
			@Override
			public Iterator<Set<TermVariable>> iterator() {

				return new Iterator<Set<TermVariable>>() {
					private Iterator<TermVariable> m_It;

					{
						m_It = unionFind.getAllRepresentatives().iterator();
					}

					@Override
					public boolean hasNext() {
						return m_It.hasNext();
					}

					@Override
					public Set<TermVariable> next() {
						return unionFind.getEquivalenceClassMembers(m_It.next());
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
					
				};
			}
		};
	}
	
	Set<Term> getTermsOfConnectedVariables(Set<TermVariable> connectedVars) {
		Set<Term> result = new HashSet<Term>();
		for (TermVariable tv : connectedVars) {
			result.addAll(m_Tv2Terms.get(tv));
		}
		return result;
	}
	
	List<Term> getTermsWithOutTvs() {
		return m_TermWithoutTvs;
	}
	
}