package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.*;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;


/**
 * Represents a non-termination argument for a lasso program in form of an
 * infinite execution.
 * 
 * It is composed of
 * <ul>
 * <li> an initial state at the begin of the lasso,
 * <li> a state at first visit of the honda,
 * <li> a ray of the loop's transition polyhedron, and
 * <li> a discount factor lambda.
 * </ul>
 * 
 * The infinite execution described by this nontermination argument is
 * 
 * state_init, state_honda,
 * state_honda + ray, state_honda + (1 + lambda) ray,
 * state_honda + (1 + lambda + lambda^2) ray, ...
 * 
 * @author Jan Leike
 */
public class NonTerminationArgument {
	
	private Map<BoogieVar, Rational> m_StateInit;
	private Map<BoogieVar, Rational> m_StateHonda;
	private Map<BoogieVar, Rational> m_Ray;
	private Rational m_Lambda;
	
	/**
	 * Construct a non-termination argument
	 * 
	 * The infinite execution described by this nontermination argument is
	 * 
	 * state_init, state_honda,
	 * state_honda + ray, state_honda + (1 + lambda) ray,
	 * state_honda + (1 + lambda + lambda^2) ray, ...
	 * 
	 * @param state_init initial state
	 * @param state_honda state at the lasso's honda
	 * @param ray ray of the lasso's polyhedron
	 * @param lambda discount factor
	 */
	public NonTerminationArgument(Map<BoogieVar, Rational> state_init,
			Map<BoogieVar, Rational> state_honda,
			Map<BoogieVar, Rational> ray,
			Rational lambda) {
		assert(state_init != null);
		m_StateInit = state_init;
		assert(state_honda != null);
		m_StateHonda = state_honda;
		assert(lambda != null);
		m_Lambda = lambda;
		assert(ray != null);
		m_Ray = ray;
	}
	
	/**
	 * @return the initial state
	 */
	public Map<BoogieVar, Rational> getStateInit() {
		return Collections.unmodifiableMap(m_StateInit);
	}
	
	/**
	 * @return the state at the lasso's honda
	 */
	public Map<BoogieVar, Rational> getStateHonda() {
		return Collections.unmodifiableMap(m_StateHonda);
	}
	
	/**
	 * @return the ray of the loop's transition polyhedron 
	 */
	public Map<BoogieVar, Rational> getRay() {
		return Collections.unmodifiableMap(m_Ray);
	}
	
	/**
	 * @return the discount factor
	 */
	public Rational getLambda() {
		return m_Lambda;
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("Non-Termination argument consisting of:\n");
		sb.append("Initial state: ");
		sb.append(m_StateInit);
		sb.append("\nHonda state: ");
		sb.append(m_StateHonda);
		sb.append("\nRay: ");
		sb.append(m_Ray);
		sb.append("\nLambda: ");
		sb.append(m_Lambda);
		return sb.toString();
	}
	
	public Expression asRecurrentSet() {
		// TODO: { state1, state1 + ray, state1 + (1 + lambda)*ray, ... }
		return null;
	}
}
