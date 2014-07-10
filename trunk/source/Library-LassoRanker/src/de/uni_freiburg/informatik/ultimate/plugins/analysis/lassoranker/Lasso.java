package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.variables.RankVar;


/**
 * 
 * This is a lasso program represented by a stem and a loop transition.
 * The state before the stem is called the initial state (init), and the
 * state after the stem, before and after the loop is called honda.
 * 
 * This is best explained using ascii art:
 * 
 * <pre>
 *                         ______
 *            stem        /      \
 * (init) ---------->  (honda)    | loop
 *                       ^        |
 *                        \______/
 * </pre>
 * 
 * @author Jan Leike
 */
public class Lasso implements Serializable {
	private static final long serialVersionUID = 8922273828007750770L;

	/**
	 * The stem transition
	 */
	private final LinearTransition m_stem;
	
	/**
	 * The loop transition
	 */
	private final LinearTransition m_loop;
	
	/**
	 * Construct a new lasso program
	 * 
	 * @param stem the stem transition, can be null
	 * @param loop the loop transition, can be null
	 */
	public Lasso(LinearTransition stem, LinearTransition loop) {
		stem = balanceVariablesStem(stem, loop);
		loop = balanceVariablesLoop(stem, loop);
		m_stem = stem == null ? LinearTransition.getTranstionTrue() : stem;
		m_loop = loop == null ? LinearTransition.getTranstionTrue() : loop;
		
	}
	
	/**
	 * @return the stem (is never null)
	 */
	public LinearTransition getStem() {
		assert m_stem != null;
		return m_stem;
	}
	
	/**
	 * @return the loop (is never null)
	 */
	public LinearTransition getLoop() {
		assert m_loop != null;
		return m_loop;
	}
	
	/**
	 * @return all RankVars that occur in the lasso
	 */
	public Collection<RankVar> getAllRankVars() {
		Collection<RankVar> rankVars = new LinkedHashSet<RankVar>();
		rankVars.addAll(m_stem.getInVars().keySet());
		rankVars.addAll(m_stem.getOutVars().keySet());
		rankVars.addAll(m_loop.getInVars().keySet());
		rankVars.addAll(m_loop.getOutVars().keySet());
		return rankVars;
	}
	
	/**
	 * Provide guesses for eigenvalues of the loop.
	 * 
	 * This procedure is neither sound nor complete:
	 * there might be eigenvalues that are not found by this procedure and
	 * this procedure might return values that are not eigenvalues of the loop.
	 * 
	 * The result of this is used as guesses for Motzkin coefficients in the
	 * termination analysis and for lambda in the nontermination analysis.
	 * This allows us to handle some more complicated examples while relying
	 * only on linear constraint solving.
	 * 
	 * This method works as follows. If there is a statement
	 * <pre>x = 2*y + 5</pre> we guess the eigenvalue 2 if we can prove
	 * that the loop disjunct implies x = y.
	 * 
	 * The returned values always contain 0 and 1.
	 * 
	 * @param include_negative whether to include negative guesses
	 * @return an array of guesses for the loop's eigenvalues
	 */
	public Rational[] guessEigenvalues(boolean include_negative) {
		Set<Rational> motzkin_coeffs = new HashSet<Rational>();
		motzkin_coeffs.add(Rational.ZERO);
		motzkin_coeffs.add(Rational.ONE);
		for (List<LinearInequality> polyhedron : m_loop.getPolyhedra()) {
			// Find aliases for variables
			Map<Term, Set<Term>> aliases = new HashMap<Term, Set<Term>>();
			for (LinearInequality li : polyhedron) {
				// If li is 0 <= a*x + b*y with a == -b and a != 0 != b
				// then put x -> y into aliases
				if (!li.isStrict() && li.getConstant().isZero()
						&& li.getVariables().size() == 2) {
					Term[] vars = li.getVariables().toArray(new Term[2]);
					AffineTerm at0 = li.getCoefficient(vars[0]);
					AffineTerm at1 = li.getCoefficient(vars[1]);
					assert !at0.isZero();
					assert !at1.isZero();
					if (at0.isConstant() && at1.isConstant()
							&& at0.getConstant().equals(at1.getConstant().negate())) {
						Term var0 = vars[0];
						Term var1 = vars[1];
						if (at0.getConstant().isNegative()) {
							// Swap var0 and var1
							Term var2 = var0;
							var0 = var1;
							var1 = var2;
						}
						if (!aliases.containsKey(var0)) {
							aliases.put(var0, new HashSet<Term>());
						}
						aliases.get(var0).add(var1);
					}
				}
			}
			
			for (Map.Entry<RankVar, Term> entry : m_loop.getOutVars().entrySet()) {
				RankVar rkVar = entry.getKey();
				Term outVar = entry.getValue();
				
				// Find possible aliases
				if (!m_loop.getInVars().containsKey(rkVar)) {
					continue;
				}
				List<Term> possible_inVars = new ArrayList<Term>();
				Term inVar = m_loop.getInVars().get(rkVar);
				possible_inVars.add(inVar);
				if (aliases.containsKey(inVar)) {
					for (Term aliasVar : aliases.get(inVar)) {
						if (aliases.containsKey(aliasVar)
								&& aliases.get(aliasVar).contains(inVar)) {
							possible_inVars.add(aliasVar);
						}
					}
				}
				
				for (LinearInequality li : polyhedron) {
					for (Term aliasVar : possible_inVars) {
						AffineTerm c_in = li.getCoefficient(aliasVar);
						AffineTerm c_out = li.getCoefficient(outVar);
						if (!c_in.isZero() && !c_out.isZero()) {
							// inVar and outVar occur in this linear inequality
							assert c_in.isConstant();
							assert c_out.isConstant();
							Rational eigenv =
									c_in.getConstant().div(c_out.getConstant()).negate();
							if (!eigenv.isNegative() || include_negative) {
								motzkin_coeffs.add(eigenv);
							}
						}
					}
				}
			}
		}
		return motzkin_coeffs.toArray(new Rational[0]);
	}
	
	/**
	 * Add all inVars of the loop as in- and outVars of the stem.
	 * 
	 * This ensures that (global) valuations for variables (e.g. those
	 * generated in the nontermination analysis) stay constant in transitions
	 * where these variables are not explicitly scoped.
	 */
	private static LinearTransition balanceVariablesStem(LinearTransition stem,
			LinearTransition loop) {
		if (stem == null || loop == null) {
			return stem; // nothing to do
		}
		// Add variables existing in the loop to the stem
		Map<RankVar, Term> addVars = new HashMap<RankVar, Term>();
		for (Map.Entry<RankVar, Term> entry : loop.getInVars().entrySet()) {
			if (!stem.getInVars().containsKey(entry.getKey()) &&
					!stem.getOutVars().containsKey(entry.getKey())) {
				addVars.put(entry.getKey(), entry.getValue());
			}
		}
		if (!addVars.isEmpty()) {
			// Because the variable maps in LinearTransition are immutable,
			// make a new transition and replace the old one
			Map<RankVar, Term> inVars =
					new HashMap<RankVar, Term>(stem.getInVars());
			Map<RankVar, Term> outVars =
					new HashMap<RankVar, Term>(stem.getOutVars());
			inVars.putAll(addVars);
			outVars.putAll(addVars);
			stem = new LinearTransition(stem.getPolyhedra(), inVars,
					outVars);
		}
		return stem;
	}
	
	/**
	 * Add all outVars of the stem as in- and outVars of the loop.
	 * 
	 * This ensures that (global) valuations for variables (e.g. those
	 * generated in the nontermination analysis) stay constant in transitions
	 * where these variables are not explicitly scoped.
	 */
	private static LinearTransition balanceVariablesLoop(LinearTransition stem,
			LinearTransition loop) {
		if (stem == null || loop == null) {
			return loop; // nothing to do
		}
		
		// Add variables existing in the stem to the loop
		Map<RankVar, Term> addVars = new HashMap<RankVar, Term>();
		for (Map.Entry<RankVar, Term> entry : stem.getOutVars().entrySet()) {
			if (!loop.getInVars().containsKey(entry.getKey()) &&
					!loop.getOutVars().containsKey(entry.getKey())) {
				addVars.put(entry.getKey(), entry.getValue());
			}
		}
		if (!addVars.isEmpty()) {
			// Because the variable maps in LinearTransition are immutable,
			// make a new transition and replace the old one
			Map<RankVar, Term> inVars =
					new HashMap<RankVar, Term>(loop.getInVars());
			Map<RankVar, Term> outVars =
					new HashMap<RankVar, Term>(loop.getOutVars());
			inVars.putAll(addVars);
			outVars.putAll(addVars);
			loop = new LinearTransition(loop.getPolyhedra(), inVars,
					outVars);
		}
		return loop;
	}
}
