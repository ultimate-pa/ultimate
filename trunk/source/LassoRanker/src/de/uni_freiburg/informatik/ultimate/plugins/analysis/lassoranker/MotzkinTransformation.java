package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.UtilExperimental;


/**
 * This class applies the equivalence transformation given by
 * Motzkin's Transposition Theorem [1].
 * 
 * Motzkin's Theorem states that a system of linear inequalities is
 * unsatisfiable if and only if a contradiction can be derived from it by the
 * means of non-negative combinations of the equations:
 * 
 * <pre>
 * ∀x. ¬(A*x ≥ b /\ B*x > d)
 * 
 * if and only if
 * 
 * ∃λ, μ. λ ≥ 0 /\ μ ≥ 0 /\ λ*A + μ*B = 0 /\ λ*b + μ*d ≥ 0 /\
 *        (λ*b > 0 \/ μ ≠ 0)
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
	 * <pre>Ax ≥ b /\ Bx > d</pre>
	 */
	private List<LinearInequality> m_inequalities;
	
	/**
	 * How many supporting invariants this should be augmented with
	 */
	private int m_numberSIneeded = 0;
	
	/**
	 * Whether the generated terms should be annotated
	 */
	private boolean m_annotate_terms = false;
	
	/**
	 * An optional description string
	 */
	public String annotation = null;
	
	/**
	 * List of Motzkin coefficients
	 */
	private List<Term> m_coefficients = null;
	
	/**
	 * Construct the MotzkinApplication object with a script instance.
	 * 
	 * After filling all the public attributes, transform() can be called,
	 * returning the formula transformed according to Motzkin's
	 * Transposition Theorem.
	 * 
	 * @param script The SMTLib script
	 */
	public MotzkinTransformation(Script script, boolean annotate) {
		m_script = script;
		m_inequalities = new ArrayList<LinearInequality>();
		m_annotate_terms = annotate;
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
	 * Add a list of linear inequalities
	 * @param l list of linear inequalities to be added to the system
	 */
	public void add_inequalities(Collection<LinearInequality> l) {
		m_inequalities.addAll(l);
	}
	
	/**
	 * Registers the Motzkin coefficients.
	 */
	private void registerMotzkinCoefficients() {
		if (m_coefficients != null) {
			// Do not register the coefficients again
			return;
		}
		
		int num_coefficients = m_inequalities.size();
		m_coefficients = new ArrayList<Term>();
		for (int i = 0; i < num_coefficients; ++i) {
			Term coefficient = AuxiliaryMethods.newConstant(m_script,
					s_motzkin_prefix + m_instance + "_" + i, "Real");
			m_coefficients.add(coefficient);
		}
	}
	
	/**
	 * Build the term corresponding to the product of the two parameters
	 * The term is build in minimalistic form for better readability.
	 * @param p the first factor
	 * @param t the second factor
	 * @return p*t as a term
	 */
	private Term product(AffineTerm a, Term t) {
		if (a.isConstant() && a.getConstant().equals(Rational.ONE)) {
			return t;
		}
		if (!a.isZero()) {
			return m_script.term("*", t, a.asRealTerm(m_script));
		}
		return null;
	}
	
	/**
	 * Applies the transformation given by Motzkin's Transposition Theorem.
	 * Call this method after adding all inequalities.
	 * 
	 * @return a formula equivalent to the negated conjunction of the
	 *         inequalities
	 */
	public Term transform() throws SMTLIBException {
		registerMotzkinCoefficients();
		int num_coefficients = m_coefficients.size();
		assert(num_coefficients == m_inequalities.size());
		
		// Gather all occurring variables
		Collection<TermVariable> vars = new HashSet<TermVariable>();
		for (LinearInequality li : m_inequalities) {
			vars.addAll(li.getVariables());
		}
		
		// Do the Motzkin transformation
		List<Term> conjunction = new ArrayList<Term>(); // Conjunctions of the
			// resulting formula
		
		// λ ≥ 0 /\ μ ≥ 0
		for (Term coefficient : m_coefficients) {
			conjunction.add(m_script.term(">=", coefficient,
					m_script.decimal("0")));
		}
		
		// λ*A + μ*B = 0
		for (TermVariable var : vars) {
			List<Term> summands = new ArrayList<Term>();
			for (int i = 0; i < num_coefficients; ++i) {
				Term s = product(m_inequalities.get(i).getCoefficient(var),
						m_coefficients.get(i));
				if (s != null) {
					summands.add(s);
				}
			}
			Term sum = UtilExperimental.sum(m_script, m_script.sort("Real"),
					summands.toArray(new Term[0]));
			conjunction.add(m_script.term("=", sum, m_script.decimal("0")));
		}
		
		// λ*b + μ*d ≤ 0
		{
			List<Term> summands = new ArrayList<Term>();
			for (int i = 0; i < num_coefficients; ++i) {
				LinearInequality li = m_inequalities.get(i);
				Term s = product(li.getConstant(), m_coefficients.get(i));
				if (s != null) {
					summands.add(s);
				}
			}
			Term sum = UtilExperimental.sum(m_script, m_script.sort("Real"),
					summands.toArray(new Term[0]));
			conjunction.add(m_script.term("<=", sum, m_script.decimal("0")));
		}
		
		{
			// λ*b < 0 -- Farkas' Lemma (no strict inequalities)
			List<Term> summands = new ArrayList<Term>();
			for (int i = 0; i < num_coefficients; ++i) {
				LinearInequality li = m_inequalities.get(i);
				Term s = product(li.getConstant(), m_coefficients.get(i));
				if (!li.isStrict() && s != null) {
					// only non-strict inequalities
					summands.add(s);
				}
			}
			Term sum = UtilExperimental.sum(m_script, m_script.sort("Real"),
					summands.toArray(new Term[0]));
			Term classical = m_script.term("<", sum, m_script.decimal("0"));
			
			// μ ≠ 0   -- strict inequalities
			summands = new ArrayList<Term>();
			for (int i = 0; i < num_coefficients; ++i) {
				LinearInequality li = m_inequalities.get(i);
				if (li.isStrict()) {
					// only strict inequalities
					summands.add(m_coefficients.get(i));
				}
			}
			sum = UtilExperimental.sum(m_script, m_script.sort("Real"),
					summands.toArray(new Term[0]));
			Term non_classical = m_script.term(">", sum, m_script.decimal("0"));
			
			conjunction.add(Util.or(m_script, classical, non_classical));
		}
		
		// Fixed Motzkin coefficients
		{
			for (int i = 0; i < num_coefficients; ++i) {
				LinearInequality li = m_inequalities.get(i);
				if (!li.needs_motzkin_coefficient) {
					Term coefficient = m_coefficients.get(i);
					conjunction.add(Util.or(m_script,
						m_script.term("=", coefficient, m_script.decimal("0")),
						m_script.term("=", coefficient, m_script.decimal("1"))
					));
					// TODO: allow fixing to { 1 }.
				}
			}
		}
		
		Term t = Util.and(m_script, conjunction.toArray(new Term[0]));
		if (m_annotate_terms) {
			t = m_script.annotate(t, new Annotation(":named", annotation));
		}
		return t;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("MotzkinApplication\n");
		if (annotation != null) {
			sb.append("Annotation: ");
			sb.append(annotation);
			sb.append("\n");
		}
		sb.append("Inequalities:");
		for (LinearInequality li : m_inequalities) {
			sb.append("\n    ");
			sb.append(li);
		}
		sb.append("\nConstraints:\n");
		sb.append(SMTPrettyPrinter.print(this.transform()));
		return sb.toString();
	}
}