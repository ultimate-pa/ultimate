package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.*;

import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.result.IResult;


/**
 * Represents a termination argument for a linear lasso program. It consists of
 * 
 * <ul>
 * <li> a ranking function, and
 * <li> a set of supporting invariants that are required to prove the ranking
 *      function.
 * </ul>
 * 
 * @author Jan Leike
 */
public class TerminationArgument implements IResult {
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
		m_supporting_invariants = supporting_invariants;
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
	
	@Override
	public ILocation getLocation() {
		return null;
	}
	
	@Override
	public String getShortDescription() {
		return "Termination argument";
	}
	
	@Override
	public String getLongDescription() {
		StringBuilder sb = new StringBuilder();
		sb.append("Termination argument consisting of:\n");
		sb.append("Ranking function ");
		sb.append(m_ranking_function);
		sb.append("\n");
		sb.append("Supporting invariants ");
		sb.append(m_supporting_invariants);
		return sb.toString();
	}
	
	public String toString() {
		return this.getLongDescription();
	}
}
