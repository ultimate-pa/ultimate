/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE LassoRanker Library.
 * 
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.termination;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lassoranker.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;
import de.uni_freiburg.informatik.ultimate.lassoranker.InstanceCounting;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality.PossibleMotzkinCoefficients;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SMTPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;


/**
 * This class applies the equivalence transformation given by
 * Motzkin's Transposition Theorem [1, Cor. 7.1k].
 * 
 * Motzkin's Theorem states that a system of linear inequalities is
 * unsatisfiable if and only if a contradiction can be derived from it by the
 * means of non-negative combinations of the equations:
 * 
 * <pre>
 * ∀x. ¬(A*x + b ≥ 0 /\ B*x + d > 0)
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
 * [1] A. Schrijver. Theory of Linear and Integer Programming.
 *     Wiley-Interscience Series in Discrete Mathematics and Optimization. 1999.
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
	private final Script mscript;
	
	/**
	 * What analysis type should be used for the termination analysis?
	 * Use a linear SMT query, use a linear SMT query but guess some eigenvalues
	 * of the loop, or use a nonlinear SMT query?
	 */
	private final AnalysisType manalysis_type;
	
	/**
	 * Whether the generated terms should be annotated.
	 * This can be helpful if you read the SMT script while debugging.
	 */
	private boolean mannotate_terms;
	
	/**
	 * List of linear inequalities
	 * <pre>Ax + b ≥ 0 /\ Bx + d > 0</pre>
	 */
	private final List<LinearInequality> minequalities;
	
	/**
	 * How many supporting invariants this should be augmented with
	 */
	private int mnumberSIneeded = 0;
	
	/**
	 * Whether the transform()-method has been called yet
	 */
	private boolean mtransformed = false;
	
	/**
	 * An optional description string
	 */
	public String annotation = null; // Must be unique!
	
	/**
	 * List of Motzkin coefficients
	 */
	private Term[] mcoefficients = null;
	
	/**
	 * For each new linear inequality there is a new unique Motzkin coefficient introduced, this map stores this relationship.
	 */
	private Map<String, LinearInequality> mMotzkinCoefficients2LinearInequalities;
	
	/**
	 * Construct the MotzkinApplication object with a script instance.
	 * 
	 * After filling all the public attributes, transform() can be called,
	 * returning the formula transformed according to Motzkin's
	 * Transposition Theorem.
	 * 
	 * @param script The SMTLib script
	 * @param linear should the transformed formula be linear?
	 * @param annotate annotate the transformed term? (This can be helpful if
	 * you read the SMT script while debugging.)
	 * 
	 */
	public MotzkinTransformation(final Script script,
			final AnalysisType termination_analysis, final boolean annotate) {
		mscript = script;
		minequalities = new ArrayList<LinearInequality>();
		mannotate_terms = annotate;
		manalysis_type = termination_analysis;
		mMotzkinCoefficients2LinearInequalities = new HashMap<>();
	}
	
	/**
	 * @return the number of supporting invariants that should be added to the
	 *         system of inequalities by the supporting invariant generator.
	 */
	public int get_number_SI_needed() {
		return mnumberSIneeded;
	}
	
	/**
	 * Set the number of supporting invariants that should be added to the
	 * system of inequalities by the supporting invariant generator.
	 * @param i number of supporting invariants (>= 0)
	 */
	public void set_number_SI_needed(final int i) {
		assert(i >= 0);
		mnumberSIneeded = i;
	}
	
	/**
	 * Add a linear inequality
	 * @param li linear inequality to be added to the system
	 */
	public void add_inequality(final LinearInequality li) {
		minequalities.add(li);
	}
	
	/**
	 * Add a list of linear inequalities
	 * @param l list of linear inequalities to be added to the system
	 */
	public void add_inequalities(final Collection<LinearInequality> l) {
		minequalities.addAll(l);
	}
	
	/**
	 * Will the given inequality need a variable for its Motzkin coefficient?
	 */
	private boolean needsMotzkinCoefficient(final LinearInequality li) {
		if (manalysis_type.isLinear()) {
			return li.allAffineTermsAreConstant();
		} else if (manalysis_type == AnalysisType.NONLINEAR) {
			return li.mMotzkinCoefficient != PossibleMotzkinCoefficients.ONE;
		} else {
			assert false;
		}
		return true;
	}
	
	/**
	 * Registers the Motzkin coefficients.
	 */
	private void registerMotzkinCoefficients() {
		if (mcoefficients != null) {
			// Do not register the coefficients again
			return;
		}
		
		final int numcoefficients = minequalities.size();
		mcoefficients = new Term[numcoefficients];
		for (int i = 0; i < numcoefficients; ++i) {
			final LinearInequality li = minequalities.get(i);
			if (needsMotzkinCoefficient(li)) {
				String motzkinCoefficientName = s_motzkin_prefix + getInstanceNumber() + "_" + i;
				final Term coefficient = SmtUtils.buildNewConstant(mscript, motzkinCoefficientName, "Real");
				mcoefficients[i] = coefficient;
				mMotzkinCoefficients2LinearInequalities.put(motzkinCoefficientName, li);
			} else {
				mcoefficients[i] = mscript.numeral(BigInteger.ONE);
			}
		}
	}
	
	/**
	 * Returns map from Motzkin coefficients to linear inequality.
	 * @return
	 */
	public Map<String, LinearInequality> getMotzkinCoefficients2LinearInequalities() {
		return mMotzkinCoefficients2LinearInequalities;
	}

	/**
	 * Build the term corresponding to the product of the two parameters
	 * The term is build in minimalistic form for better readability.
	 * @param p the first factor
	 * @param t the second factor
	 * @return p*t as a term
	 */
	private Term product(final AffineTerm a, final Term t) {
		if (a.isConstant() && a.getConstant().equals(Rational.ONE)) {
			return t;
		}
		if (!a.isZero()) {
			return mscript.term("*", t, a.asRealTerm(mscript));
		}
		return null;
	}
	
	private Term doTransform(final Term[] coefficients, final Collection<Term> vars)
			throws SMTLIBException {
		final int numcoefficients = coefficients.length;
		assert(numcoefficients == minequalities.size());
		
		final List<Term> conjunction = new ArrayList<Term>(); // Conjunction of the
			// resulting formula
		
		// λ*A + μ*B = 0
		for (final Term var : vars) {
			final List<Term> summands = new ArrayList<Term>();
			for (int i = 0; i < numcoefficients; ++i) {
				final Term s = product(minequalities.get(i).getCoefficient(var),
						coefficients[i]);
				if (s != null) {
					summands.add(s);
				}
			}
			final Term sum = SmtUtils.sum(mscript, mscript.sort("Real"),
					summands.toArray(new Term[summands.size()]));
			conjunction.add(mscript.term("=", sum, mscript.decimal("0")));
		}
		
		// λ*b + μ*d ≤ 0
		{
			final List<Term> summands = new ArrayList<Term>();
			for (int i = 0; i < numcoefficients; ++i) {
				final LinearInequality li = minequalities.get(i);
				final Term s = product(li.getConstant(), coefficients[i]);
				if (s != null) {
					summands.add(s);
				}
			}
			final Term sum = SmtUtils.sum(mscript, mscript.sort("Real"),
					summands.toArray(new Term[summands.size()]));
			conjunction.add(mscript.term("<=", sum, mscript.decimal("0")));
		}
		
		{
			// λ*b < 0 -- Farkas' Lemma (no strict inequalities)
			List<Term> summands = new ArrayList<Term>();
			for (int i = 0; i < numcoefficients; ++i) {
				final LinearInequality li = minequalities.get(i);
				final Term s = product(li.getConstant(), coefficients[i]);
				if (!li.isStrict() && s != null) {
					// only non-strict inequalities
					summands.add(s);
				}
			}
			final Term sum = SmtUtils.sum(mscript, mscript.sort("Real"),
					summands.toArray(new Term[summands.size()]));
			final Term classical = mscript.term("<", sum, mscript.decimal("0"));
			
			// μ ≠ 0   -- strict inequalities
			// since all μ are nonnegative, we can use sum(μ) > 0 equivalently
			summands = new ArrayList<Term>();
			for (int i = 0; i < numcoefficients; ++i) {
				final LinearInequality li = minequalities.get(i);
				if (li.isStrict()) {
					// only strict inequalities
					summands.add(coefficients[i]);
				}
			}
			final Term non_classical = mscript.term(">",
					SmtUtils.sum(mscript, mscript.sort("Real"),
							summands.toArray(new Term[summands.size()])),
					mscript.decimal("0"));
			
			conjunction.add(Util.or(mscript, classical, non_classical));
			return Util.and(mscript, conjunction.toArray(new Term[conjunction.size()]));
		}
	}
	
	/**
	 * Applies the transformation given by Motzkin's Transposition Theorem.
	 * Call this method after adding all inequalities.
	 * 
	 * @return a formula equivalent to the negated conjunction of the
	 *         inequalities
	 */
	public Term transform(final Rational[] motzkin_guesses) throws SMTLIBException {
		mtransformed = true;
		registerMotzkinCoefficients();
		
		// Gather all occurring variables
		final Collection<Term> vars = new LinkedHashSet<Term>();
		for (final LinearInequality li : minequalities) {
			vars.addAll(li.getVariables());
		}
		
		final List<Term> conjunction = new ArrayList<Term>();
		
		// λ ≥ 0 /\ μ ≥ 0
		for (final Term coefficient : mcoefficients) {
			if (coefficient != null) {
				conjunction.add(mscript.term(">=", coefficient,
						mscript.decimal("0")));
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
		if (manalysis_type.isLinear()) {
			// Count the number of Motzkin coefficients that need to be fixed
			int numfixed_coeffs = 0;
			final int[] fixed_indeces = new int[mcoefficients.length];
				// This array is way to big, but I don't care
			for (int i = 0; i < minequalities.size(); ++i) {
				final LinearInequality li = minequalities.get(i);
				if (!needsMotzkinCoefficient(li) && li.mMotzkinCoefficient
						!= PossibleMotzkinCoefficients.ONE) {
					fixed_indeces[numfixed_coeffs] = i;
					++numfixed_coeffs;
				}
			}
			assert numfixed_coeffs < 31 : "Too many fixed coefficients!";
			
			// Create a new coefficients array so that we can edit it
			final Term[] fixed_coefficients = new Term[mcoefficients.length];
			System.arraycopy(mcoefficients, 0, fixed_coefficients, 0, mcoefficients.length);
			
			if (manalysis_type.wantsGuesses() && motzkin_guesses.length > 0) {
				// Convert Motzkin coefficients from Rationals into Terms
				final Term[] motzkin_coeffs = new Term[motzkin_guesses.length];
				for (int i = 0; i < motzkin_guesses.length; ++i) {
					motzkin_coeffs[i] = motzkin_guesses[i].toTerm(mscript.sort("Real"));
				}
				
				final int[] cases = new int[numfixed_coeffs]; // initialized to 0 by default
				final List<Term> disjunction = new ArrayList<Term>();
				if (numfixed_coeffs == 0) {
					disjunction.add(doTransform(fixed_coefficients, vars));
				} else {
					while (cases[numfixed_coeffs - 1] < motzkin_guesses.length) {
						// Update the coefficients array
						for (int j = 0; j < numfixed_coeffs; ++j) {
							fixed_coefficients[fixed_indeces[j]] =
									motzkin_coeffs[cases[j]];
						}
						disjunction.add(doTransform(fixed_coefficients, vars));
						// Increment the cases counter
						int i = 0;
						while (i < numfixed_coeffs) {
							++cases[i];
							if (i < numfixed_coeffs - 1 && cases[i] >= motzkin_guesses.length) {
								cases[i] = 0;
								++i;
							} else {
								break;
							}
						}
					}
				}
				conjunction.add(
						Util.or(mscript, disjunction.toArray(new Term[disjunction.size()])));
			} else {
				// Fixed values
				final Term zero = mscript.decimal("0");
				final Term one = mscript.decimal("1");
				
				final List<Term> disjunction = new ArrayList<Term>();
				for (int i = 0; i < (1 << numfixed_coeffs); ++i) {
					// Update the coefficients array
					for (int j = 0; j < numfixed_coeffs; ++j) {
						fixed_coefficients[fixed_indeces[j]] =
								(i & (1 << j)) == 0 ? zero : one;
					}
					disjunction.add(doTransform(fixed_coefficients, vars));
				}
				conjunction.add(
						Util.or(mscript, disjunction.toArray(new Term[disjunction.size()])));
			}
		} else if (manalysis_type == AnalysisType.NONLINEAR) {
			conjunction.add(doTransform(mcoefficients, vars));
			
			// Fixed Motzkin coefficients
			for (int i = 0; i < minequalities.size(); ++i) {
				final LinearInequality li = minequalities.get(i);
				if (li.mMotzkinCoefficient
						== PossibleMotzkinCoefficients.ZERO_AND_ONE) {
					// Fixing Motzkin coefficient to { 0, 1 }
					conjunction.add(Util.or(mscript,
						mscript.term("=",
								mcoefficients[i], mscript.decimal("0")),
						mscript.term("=",
								mcoefficients[i], mscript.decimal("1"))
					));
				}
			}
		} else {
			assert false;
		}
		Term t = Util.and(mscript, conjunction.toArray(new Term[conjunction.size()]));
		
		// Possibly annotate the term
		if (mannotate_terms && annotation != null) {
			t = mscript.annotate(t, new Annotation(":named",
					annotation.replace(" ", "_")));
		}
		return t;
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("MotzkinApplication\n");
		if (annotation != null) {
			sb.append("Annotation: ");
			sb.append(annotation);
			sb.append("\n");
		}
		sb.append("Inequalities:");
		for (final LinearInequality li : minequalities) {
			sb.append("\n    ");
			sb.append(li);
		}
		if (mtransformed) {
			sb.append("\nConstraints:\n");
			final boolean annotate_terms = mannotate_terms;
			mannotate_terms = false;
			sb.append(new SMTPrettyPrinter(transform(new Rational[0])));
			mannotate_terms = annotate_terms;
		}
		return sb.toString();
	}
}
