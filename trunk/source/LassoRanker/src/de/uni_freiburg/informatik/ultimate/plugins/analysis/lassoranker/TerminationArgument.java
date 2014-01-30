package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.RankingFunction;


/**
 * Represents a termination argument for a lasso program.
 * 
 * The termination argument consists of
 * <ul>
 * <li> a ranking function, and
 * <li> a set of supporting invariants that are required to prove the ranking
 *      function.
 * </ul>
 * 
 * @author Jan Leike
 */
public class TerminationArgument {
	private RankingFunction m_ranking_function;
	private Collection<SupportingInvariant> m_supporting_invariants;
	
	/**
	 * Construct a termination argument
	 * @param ranking_function a ranking function
	 * @param supporting_invariants a collection of required supporting
	 *                              invariants
	 */
	public TerminationArgument(RankingFunction ranking_function,
			Collection<SupportingInvariant> supporting_invariants) {
		assert(ranking_function != null);
		m_ranking_function = ranking_function;
		assert(supporting_invariants != null);
		
		// Add only non-trivial supporting invariants
		m_supporting_invariants = new ArrayList<SupportingInvariant>();
		for (SupportingInvariant si : supporting_invariants) {
			if (!si.isTrue()) {
				m_supporting_invariants.add(si);
			}
		}
		
	}
	
	/**
	 * @return the ranking function
	 */
	public RankingFunction getRankingFunction() {
		return m_ranking_function;
	}
	
	/**
	 * @return the supporting invariants
	 */
	public Collection<SupportingInvariant> getSupportingInvariants() {
		return Collections.unmodifiableCollection(m_supporting_invariants);
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("Termination argument consisting of:\n");
		sb.append("Ranking function ");
		sb.append(m_ranking_function);
		sb.append("\n");
		sb.append("Supporting invariants ");
		sb.append(m_supporting_invariants);
		return sb.toString();
	}
}
