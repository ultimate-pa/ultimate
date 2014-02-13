/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
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
	private boolean m_annotate_terms;
	
	/**
	 * Whether the transformed formula should be linear
	 */
	private boolean m_linear;
	
	/**
	 * An optional description string
	 */
	public String annotation = null; // Must be unique!
	
	/**
	 * List of Motzkin coefficients
	 */
	private Term[] m_coefficients = null;
	
	/**
	 * Construct the MotzkinApplication object with a script instance.
	 * 
	 * After filling all the public attributes, transform() can be called,
	 * returning the formula transformed according to Motzkin's
	 * Transposition Theorem.
	 * 
	 * @param script The SMTLib script
	 * @param linear should the transformed formula be linear?
	 * @param annotate annotate the transformed term?
	 */
	public MotzkinTransformation(Script script, boolean linear,
			boolean annotate) {
		m_script = script;
		m_inequalities = new ArrayList<LinearInequality>();
		m_annotate_terms = annotate;
		m_linear = linear;
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
		m_coefficients = new Term[num_coefficients];
		for (int i = 0; i < num_coefficients; ++i) {
			if (m_inequalities.get(i).needs_motzkin_coefficient || !m_linear) {
				Term coefficient = AuxiliaryMethods.newConstant(m_script,
						s_motzkin_prefix + m_instance + "_" + i, "Real");
				m_coefficients[i] = coefficient;
			}
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
	
	private Term doTransform(Term[] coefficients, Collection<TermVariable> vars)
			throws SMTLIBException {
		int num_coefficients = coefficients.length;
		assert(num_coefficients == m_inequalities.size());
		
		List<Term> conjunction = new ArrayList<Term>(); // Conjunction of the
			// resulting formula
		
		// λ*A + μ*B = 0
		for (TermVariable var : vars) {
			List<Term> summands = new ArrayList<Term>();
			for (int i = 0; i < num_coefficients; ++i) {
				Term s = product(m_inequalities.get(i).getCoefficient(var),
						coefficients[i]);
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
				Term s = product(li.getConstant(), coefficients[i]);
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
				Term s = product(li.getConstant(), coefficients[i]);
				if (!li.isStrict() && s != null) {
					// only non-strict inequalities
					summands.add(s);
				}
			}
			Term sum = UtilExperimental.sum(m_script, m_script.sort("Real"),
					summands.toArray(new Term[0]));
			Term classical = m_script.term("<", sum, m_script.decimal("0"));
			
			// μ ≠ 0   -- strict inequalities
			// since all μ are nonnegative, we can use sum(μ) > 0 equivalently
			summands = new ArrayList<Term>();
			for (int i = 0; i < num_coefficients; ++i) {
				LinearInequality li = m_inequalities.get(i);
				if (li.isStrict()) {
					// only strict inequalities
					summands.add(coefficients[i]);
				}
			}
			Term non_classical = m_script.term(">",
					UtilExperimental.sum(m_script, m_script.sort("Real"),
							summands.toArray(new Term[0])),
					m_script.decimal("0"));
			
			conjunction.add(Util.or(m_script, classical, non_classical));
			return Util.and(m_script, conjunction.toArray(new Term[0]));
		}
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
		
		// Gather all occurring variables
		Collection<TermVariable> vars = new HashSet<TermVariable>();
		for (LinearInequality li : m_inequalities) {
			vars.addAll(li.getVariables());
		}
		
		List<Term> conjunction = new ArrayList<Term>();
		
		// λ ≥ 0 /\ μ ≥ 0
		for (Term coefficient : m_coefficients) {
			if (coefficient != null) {
				conjunction.add(m_script.term(">=", coefficient,
						m_script.decimal("0")));
			}
		}
		
		/*
		 * With a nonlinear query, we think it is more efficient to
		 * use variables for Motzkin coefficients that are fixed to
		 * { 0, 1 } and fix them to those two values later on.
		 * 
		 * This cannot be done when we need a linear query, so we have to
		 * build a big disjunction.
		 */
		if (m_linear) {
			// Count the number of Motzkin coefficients that need to be fixed
			int num_fixed_coeffs = 0;
			int[] fixed_indeces = new int[m_coefficients.length];
				// This array is way to big, but I don't care
			for (int i = 0; i < m_inequalities.size(); ++i) {
				LinearInequality li = m_inequalities.get(i);
				if (!li.needs_motzkin_coefficient
						&& li.motzkin_coefficient_can_be_zero) {
					fixed_indeces[num_fixed_coeffs] = i;
					++num_fixed_coeffs;
				}
			}
			assert num_fixed_coeffs < 31 : "Too many fixed coefficients!";
			
			// Fixed values
			Term zero = m_script.decimal("0");
			Term one = m_script.decimal("1");
			
			// Create a new coefficients array so that we can edit it
			Term[] fixed_coefficients = new Term[m_coefficients.length];
			for (int i = 0; i < m_coefficients.length; ++i) {
				if (m_inequalities.get(i).motzkin_coefficient_can_be_zero) {
					fixed_coefficients[i] = m_coefficients[i];
				} else {
					fixed_coefficients[i] = one;
				}
			}
			
			List<Term> disjunction = new ArrayList<Term>();
			for (int i = 0; i < (1 << num_fixed_coeffs); ++i) {
				// Update the coefficients array
				for (int j = 0; j < num_fixed_coeffs; ++j) {
					fixed_coefficients[fixed_indeces[j]] =
							(i & (1 << j)) == 0 ? zero : one;
				}
				disjunction.add(doTransform(fixed_coefficients, vars));
			}
			conjunction.add(
					Util.or(m_script, disjunction.toArray(new Term[0])));
		} else {
			assert !m_linear;
			conjunction.add(doTransform(m_coefficients, vars));
			
			// Fixed Motzkin coefficients
			{
				for (int i = 0; i < m_inequalities.size(); ++i) {
					LinearInequality li = m_inequalities.get(i);
					if (!li.needs_motzkin_coefficient) {
						Term coefficient = m_coefficients[i];
						if (li.motzkin_coefficient_can_be_zero) {
							// Fixing Motzkin coefficient to { 0, 1 }
							conjunction.add(Util.or(m_script,
								m_script.term("=",
										coefficient, m_script.decimal("0")),
								m_script.term("=",
										coefficient, m_script.decimal("1"))
							));
						} else {
							// Fixing Motzkin coefficient to { 1 }
							conjunction.add(m_script.term("=",
									coefficient, m_script.decimal("1")));
						}
					}
				}
			}
		}
		Term t = Util.and(m_script, conjunction.toArray(new Term[0]));
		
		// Possibly annotate the term
		if (m_annotate_terms && annotation != null) {
			t = m_script.annotate(t, new Annotation(":named",
					annotation.replace(" ", "_")));
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
		boolean annotate_terms = m_annotate_terms;
		m_annotate_terms = false;
		sb.append(SMTPrettyPrinter.print(this.transform()));
		m_annotate_terms = annotate_terms;
		return sb.toString();
	}
}