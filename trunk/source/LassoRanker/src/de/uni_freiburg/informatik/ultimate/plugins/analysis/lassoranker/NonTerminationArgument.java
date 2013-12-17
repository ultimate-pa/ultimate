package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.*;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.IResult;


/**
 * Represents a non-termination argument in form of an infinite execution
 * of the lasso program. It is composed of
 * 
 * <ul>
 * <li> an execution of the stem, i.e., up until the first node occuring
 *   infinitely often,
 * <li> an execution of the loop, and
 * <li> a recurrent set.
 * </ul>
 * 
 * @author Jan Leike
 */
public class NonTerminationArgument implements IResult {
	
	private Map<BoogieVar, Rational> m_state0;
	private Map<BoogieVar, Rational> m_state1;
	private Map<BoogieVar, Rational> m_ray;
	
	public NonTerminationArgument(Map<BoogieVar, Rational> state0,
			Map<BoogieVar, Rational> state1, Map<BoogieVar, Rational> ray) {
		assert(state0 != null);
		m_state0 = state0;
		assert(state1 != null);
		m_state1 = state1;
		assert(ray != null);
		m_ray = ray;
	}
	
	@Override
	public ILocation getLocation() {
		return null;
	}
	
	@Override
	public String getShortDescription() {
		return "Non-Termination Argument";
	}
	
	@Override
	public String getLongDescription() {
		StringBuilder sb = new StringBuilder();
		sb.append("Non-Termination argument consisting of:\n");
		sb.append(m_state0);
		sb.append("\n");
		sb.append(m_state1);
		sb.append("\n");
		sb.append(m_ray);
		return sb.toString();
	}
	
	public String toString() {
		return this.getLongDescription();
	}
	
	public Expression asRecurrentSet() {
		// TODO
		return null;
	}
}
