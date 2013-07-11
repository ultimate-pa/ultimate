package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.*;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;


/**
 * This class applies the equivalence transformation given by
 * Motzkin's Transposition Theorem [1].
 * 
 * Motzkin's Theorem states that a system of linear inequalities is
 * unsatisfiable if and only if a contradiction can be derived from it by the
 * means of non-negative combinations of the equations:
 * 
 * <pre>
 * ∀x. ¬(A*x ≤ b /\ B*x < d)
 * 
 * if and only if
 * 
 * ∃λ, μ. λ ≥ 0 /\ μ ≥ 0 /\ λ*A + μ*B = 0 /\ λ*b + μ*d ≤ 0 /\
 *        (λ*b < 0 \/ μ ≠ 0)
 * </pre>
 * 
 * Here A and B are matrices, x, b and d are column vectors, and
 * λ and μ are row vectors.
 * 
 * Note that the quantifiers are not part of this class and are for
 * illustration purposes only.
 * 
 * [1] A. Schrijver. Theory of linear and integer programming.
 * Wiley-Interscience series in discrete mathematics and optimization. 1999.
 * 
 * @author Jan Leike
 */
public class MotzkinTransformation extends InstanceCounting {
	/**
	 * Prefix for the Motzkin coefficients λ and μ
	 */
	private static final String s_motzkin_prefix = "motzkin_";
	
	/**
	 * The SMTLib script
	 */
	private Script m_script;
	
	/**
	 * List of linear inequalities
	 * Ax <= b /\ Bx < d
	 */
	private List<LinearInequality> m_inequalities;
	
	/**
	 * How many supporting invariants this should be augmented with
	 */
	private int m_numberSIneeded = 0;
	
	/**
	 * Construct the MotzkinApplication object with a script instance.
	 * 
	 * After filling all the public attributes, transform() can be called,
	 * returning the formula transformed according to Motzkin's
	 * Transposition Theorem.
	 * 
	 * @param script The SMTLib script
	 */
	public MotzkinTransformation(Script script) {
		m_script = script;
		m_inequalities = new ArrayList<LinearInequality>();
	}
	
	/**
	 * @return the number of supporting invariants that should be added to the
	 *         system of inequalities by the supporting invariant generator.
	 */
	public int get_number_SI_needed() {
		return m_numberSIneeded;
	}
	
	/**
	 * Set the number of supporting invariants that should be added to the
	 * system of inequalities by the supporting invariant generator.
	 * @param i number of supporting invariants (>= 0)
	 */
	public void set_number_SI_needed(int i) {
		assert(i >= 0);
		m_numberSIneeded = i;
	}
	
	/**
	 * Add a linear inequality
	 * @param li linear inequality to be added to the system
	 */
	public void add_inequality(LinearInequality li) {
		m_inequalities.add(li);
	}
	
	/**
	 * Applies the transformation given by Motzkin's Transposition Theorem.
	 * Call this method after adding all inequalities.
	 * 
	 * @return a formula equivalent to the negated conjunction of the
	 *         inequalities
	 */
	public Term transform() throws SMTLIBException {
		int num_coefficients = m_inequalities.size();
		
		// Register the new coefficients
		List<Term> coefficients = new ArrayList<Term>(); // Motzkin coefficients
		for (int i = 0; i < num_coefficients; ++i) {
			Term coefficient = AuxiliaryMethods.newRealConstant(m_script,
					s_motzkin_prefix + m_instance + "_" + i);
			coefficients.add(coefficient);
		}
		
		// Gather all occurring variables
		Collection<TermVariable> vars = new HashSet<TermVariable>();
		for (LinearInequality li : m_inequalities) {
			vars.addAll(li.getVariables());
		}
		
		// Do the Motzkin transformation
		List<Term> conjunction = new ArrayList<Term>(); // Conjunctions of the
			// resulting formula
		
		// λ ≥ 0 /\ μ ≥ 0
		for (Term coefficient : coefficients) {
			conjunction.add(m_script.term(">=", coefficient,
					m_script.decimal("0")));
		}
		
		// λ*A + μ*B = 0
		for (TermVariable var : vars) {
			Term[] summands = new Term[num_coefficients];
			for (int i = 0; i < num_coefficients; ++i) {
				LinearInequality li = m_inequalities.get(i);
				Term coefficient = coefficients.get(i);
				summands[i] = m_script.term("*", coefficient,
						li.getCoefficient(var));
			}
			Term sum = Util.sum(m_script, summands);
			conjunction.add(m_script.term("=", sum, m_script.decimal("0")));
		}
		
		// λ*b + μ*d ≤ 0
		{
			Term[] summands = new Term[num_coefficients];
			for (int i = 0; i < num_coefficients; ++i) {
				LinearInequality li = m_inequalities.get(i);
				Term coefficient = coefficients.get(i);
				summands[i] = m_script.term("*", coefficient, li.getConstant());
			}
			Term sum = Util.sum(m_script, summands);
			conjunction.add(m_script.term("<=", sum, m_script.decimal("0")));
		}
		
		{
			// λ*b < 0 -- Farkas' Lemma (no strict inequalities)
			List<Term> summands = new ArrayList<Term>();
			for (int i = 0; i < num_coefficients; ++i) {
				LinearInequality li = m_inequalities.get(i);
				Term coefficient = coefficients.get(i);
				if (!li.strict) {
					// only non-strict inequalities
					summands.add(m_script.term("*", coefficient,
							li.getConstant()));
				}
			}
			Term sum = Util.sum(m_script, summands.toArray(new Term[0]));
			Term classical = m_script.term("<", sum, m_script.decimal("0"));
			
			// μ ≠ 0   -- strict inequalities
			summands = new ArrayList<Term>();
			for (int i = 0; i < num_coefficients; ++i) {
				LinearInequality li = m_inequalities.get(i);
				Term coefficient = coefficients.get(i);
				if (li.strict) {
					// only strict inequalities
					summands.add(coefficient);
				}
			}
			sum = Util.sum(m_script, summands.toArray(new Term[0]));
			Term non_classical = m_script.term(">", sum, m_script.decimal("0"));
			
			conjunction.add(Util.or(m_script, classical, non_classical));
		}
		
		// Fixed Motzkin coefficients
		{
			for (int i = 0; i < num_coefficients; ++i) {
				LinearInequality li = m_inequalities.get(i);
				if (!li.m_needs_motzkin_coefficient) {
					Term coefficient = coefficients.get(i);
					conjunction.add(Util.or(m_script,
						m_script.term("=", coefficient, m_script.decimal("0")),
						m_script.term("=", coefficient, m_script.decimal("1"))
					));
					// TODO: allow fixing to { 1 }.
				}
			}
		}
		
		return Util.and(m_script, conjunction.toArray(new Term[0]));
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("Inequalities before the Motzkin transformation:\n");
		for (LinearInequality li : m_inequalities) {
			sb.append("    ");
			sb.append(li);
			sb.append("\n");
		}
		sb.append("\n");
		
		ApplicationTerm formula = (ApplicationTerm)transform();
		sb.append("Formula after the transformation:\n");
		for (Term t : formula.getParameters()) {
			sb.append("    ");
			sb.append(t);
			sb.append("\n");
		}
		
		return sb.toString();
	}
}