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

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;
import de.uni_freiburg.informatik.ultimate.lassoranker.InstanceCounting;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality.PossibleMotzkinCoefficients;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SMTPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * This class applies the equivalence transformation given by Motzkin's Transposition Theorem [1, Cor. 7.1k].
 *
 * Motzkin's Theorem states that a system of linear inequalities is unsatisfiable if and only if a contradiction can be
 * derived from it by the means of non-negative combinations of the equations:
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
 * Here A and B are matrices, x, b and d are column vectors, and λ and μ are row vectors.
 *
 * Note that the quantifiers are not part of this class and are for illustration purposes only.
 *
 * [1] A. Schrijver. Theory of Linear and Integer Programming. Wiley-Interscience Series in Discrete Mathematics and
 * Optimization. 1999.
 *
 * @author Jan Leike
 */
public class MotzkinTransformation extends InstanceCounting {
	/**
	 * Prefix for the Motzkin coefficients λ and μ
	 */
	private static final String MOTZKIN_PREFIX = "motzkin_";

	/**
	 * The SMTLib script
	 */
	private final Script mScript;

	/**
	 * What analysis type should be used for the termination analysis? Use a linear SMT query, use a linear SMT query
	 * but guess some eigenvalues of the loop, or use a nonlinear SMT query?
	 */
	private final AnalysisType mAnalysisType;

	/**
	 * Whether the generated terms should be annotated. This can be helpful if you read the SMT script while debugging.
	 */
	private boolean mAnnotateTerms;

	/**
	 * List of linear inequalities
	 *
	 * <pre>
	 * Ax + b ≥ 0 /\ Bx + d > 0
	 * </pre>
	 */
	private final List<LinearInequality> mInequalities;

	/**
	 * How many supporting invariants this should be augmented with
	 */
	private int mNumberSINeeded = 0;

	/**
	 * Whether the transform()-method has been called yet
	 */
	private boolean mTransformed = false;

	/**
	 * An optional description string (must be unique)
	 */
	public String mAnnotation = null;

	/**
	 * List of Motzkin coefficients
	 */
	private Term[] mCoefficients = null;

	/**
	 * For each new linear inequality there is a new unique Motzkin coefficient introduced, this map stores this
	 * relationship.
	 */
	private final Map<String, LinearInequality> mMotzkinCoefficients2LinearInequalities;
	
	private final IUltimateServiceProvider mServices;

	/**
	 * Construct the MotzkinApplication object with a script instance.
	 *
	 * After filling all the public attributes, transform() can be called, returning the formula transformed according
	 * to Motzkin's Transposition Theorem.
	 * @param script
	 *            The SMTLib script
	 * @param linear
	 *            should the transformed formula be linear?
	 * @param annotate
	 *            annotate the transformed term? (This can be helpful if you read the SMT script while debugging.)
	 *
	 */
	public MotzkinTransformation(final IUltimateServiceProvider services, final Script script,
			final AnalysisType terminationAnalysis, final boolean annotate) {
		mServices = services;
		mScript = script;
		mInequalities = new ArrayList<>();
		mAnnotateTerms = annotate;
		mAnalysisType = terminationAnalysis;
		mMotzkinCoefficients2LinearInequalities = new HashMap<>();
	}

	/**
	 * @return the number of supporting invariants that should be added to the system of inequalities by the supporting
	 *         invariant generator.
	 */
	public int getNumberSINeeded() {
		return mNumberSINeeded;
	}

	/**
	 * Set the number of supporting invariants that should be added to the system of inequalities by the supporting
	 * invariant generator.
	 *
	 * @param i
	 *            number of supporting invariants (>= 0)
	 */
	public void setNumberSINeeded(final int i) {
		assert i >= 0;
		mNumberSINeeded = i;
	}

	/**
	 * Add a linear inequality
	 *
	 * @param li
	 *            linear inequality to be added to the system
	 */
	public void addInequality(final LinearInequality li) {
		mInequalities.add(li);
	}

	/**
	 * Add a list of linear inequalities
	 *
	 * @param l
	 *            list of linear inequalities to be added to the system
	 */
	public void addInequalities(final Collection<LinearInequality> l) {
		mInequalities.addAll(l);
	}

	/**
	 * Will the given inequality need a variable for its Motzkin coefficient?
	 */
	private boolean needsMotzkinCoefficient(final LinearInequality li) {
		if (mAnalysisType.isLinear()) {
			return li.allAffineTermsAreConstant();
		} else if (mAnalysisType == AnalysisType.NONLINEAR) {
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
		if (mCoefficients != null) {
			// Do not register the coefficients again
			return;
		}

		final int numcoefficients = mInequalities.size();
		mCoefficients = new Term[numcoefficients];
		for (int i = 0; i < numcoefficients; ++i) {
			final LinearInequality li = mInequalities.get(i);
			if (needsMotzkinCoefficient(li)) {
				final String motzkinCoefficientName = MOTZKIN_PREFIX + getInstanceNumber() + "_" + i;
				final Term coefficient =
						SmtUtils.buildNewConstant(mScript, motzkinCoefficientName, SmtSortUtils.REAL_SORT);
				mCoefficients[i] = coefficient;
				mMotzkinCoefficients2LinearInequalities.put(motzkinCoefficientName, li);
			} else {
				mCoefficients[i] = mScript.decimal(BigDecimal.ONE);
			}
		}
	}

	/**
	 * Returns map from Motzkin coefficients to linear inequality.
	 *
	 * @return
	 */
	public Map<String, LinearInequality> getMotzkinCoefficients2LinearInequalities() {
		return mMotzkinCoefficients2LinearInequalities;
	}

	/**
	 * Build the term corresponding to the product of the two parameters The term is build in minimalistic form for
	 * better readability.
	 *
	 * @param p
	 *            the first factor
	 * @param t
	 *            the second factor
	 * @return p*t as a term
	 */
	private Term product(final AffineTerm a, final Term t) {
		if (a.isConstant() && a.getConstant().equals(Rational.ONE)) {
			return t;
		}
		if (!a.isZero()) {
			return mScript.term("*", t, a.asRealTerm(mScript));
		}
		return null;
	}

	private Term doTransform(final Term[] coefficients, final Collection<Term> vars) {
		final int numcoefficients = coefficients.length;
		assert numcoefficients == mInequalities.size();

		// Conjunction of the resulting formula
		final List<Term> conjunction = new ArrayList<>();

		// λ*A + μ*B = 0
		for (final Term var : vars) {
			final List<Term> summands = new ArrayList<>();
			for (int i = 0; i < numcoefficients; ++i) {
				final Term s = product(mInequalities.get(i).getCoefficient(var), coefficients[i]);
				if (s != null) {
					summands.add(s);
				}
			}
			final Term sum = SmtUtils.sum(mScript, SmtSortUtils.getRealSort(mScript),
					summands.toArray(new Term[summands.size()]));
			conjunction.add(mScript.term("=", sum, mScript.decimal("0")));
		}

		// λ*b + μ*d ≤ 0
		{
			final List<Term> summands = new ArrayList<>();
			for (int i = 0; i < numcoefficients; ++i) {
				final LinearInequality li = mInequalities.get(i);
				final Term s = product(li.getConstant(), coefficients[i]);
				if (s != null) {
					summands.add(s);
				}
			}
			final Term sum = SmtUtils.sum(mScript, SmtSortUtils.getRealSort(mScript),
					summands.toArray(new Term[summands.size()]));
			conjunction.add(mScript.term("<=", sum, mScript.decimal("0")));
		}

		{
			// λ*b < 0 -- Farkas' Lemma (no strict inequalities)
			List<Term> summands = new ArrayList<>();
			for (int i = 0; i < numcoefficients; ++i) {
				final LinearInequality li = mInequalities.get(i);
				final Term s = product(li.getConstant(), coefficients[i]);
				if (!li.isStrict() && s != null) {
					// only non-strict inequalities
					summands.add(s);
				}
			}
			final Term sum = SmtUtils.sum(mScript, SmtSortUtils.getRealSort(mScript),
					summands.toArray(new Term[summands.size()]));
			final Term classical = mScript.term("<", sum, mScript.decimal("0"));

			// μ ≠ 0 -- strict inequalities
			// since all μ are nonnegative, we can use sum(μ) > 0 equivalently
			summands = new ArrayList<>();
			for (int i = 0; i < numcoefficients; ++i) {
				final LinearInequality li = mInequalities.get(i);
				if (li.isStrict()) {
					// only strict inequalities
					summands.add(coefficients[i]);
				}
			}
			final Term nonClassical = mScript.term(">", SmtUtils.sum(mScript, SmtSortUtils.getRealSort(mScript),
					summands.toArray(new Term[summands.size()])), mScript.decimal("0"));

			conjunction.add(SmtUtils.or(mScript, classical, nonClassical));
			return SmtUtils.and(mScript, conjunction.toArray(new Term[conjunction.size()]));
		}
	}

	/**
	 * Applies the transformation given by Motzkin's Transposition Theorem. Call this method after adding all
	 * inequalities.
	 *
	 * TODO: fix documentation
	 * @return a formula equivalent to the negated conjunction of the inequalities
	 */
	public Term transform(final Rational[] motzkinGuesses) {
		mTransformed = true;
		registerMotzkinCoefficients();

		// Gather all occurring variables
		final Collection<Term> vars = new LinkedHashSet<>();
		for (final LinearInequality li : mInequalities) {
			vars.addAll(li.getVariables());
		}

		final List<Term> conjunction = new ArrayList<>();

		// λ ≥ 0 /\ μ ≥ 0
		for (final Term coefficient : mCoefficients) {
			if (coefficient != null) {
				conjunction.add(mScript.term(">=", coefficient, mScript.decimal("0")));
			}
		}

		/*
		 * With a nonlinear query, we think it is more efficient to use variables for Motzkin coefficients that are
		 * fixed to { 0, 1 } and fix them to those two values later on.
		 *
		 * This cannot be done when we need a linear query, so we have to build a big disjunction.
		 */
		if (mAnalysisType.isLinear()) {
			// Count the number of Motzkin coefficients that need to be fixed
			int numfixedCoeffs = 0;
			final int[] fixedIndices = new int[mCoefficients.length];
			// This array is way to big, but I don't care
			for (int i = 0; i < mInequalities.size(); ++i) {
				final LinearInequality li = mInequalities.get(i);
				if (!needsMotzkinCoefficient(li) && li.mMotzkinCoefficient != PossibleMotzkinCoefficients.ONE) {
					fixedIndices[numfixedCoeffs] = i;
					++numfixedCoeffs;
				}
			}
			assert numfixedCoeffs < 31 : "Too many fixed coefficients!";

			// Create a new coefficients array so that we can edit it
			final Term[] fixedCoefficients = new Term[mCoefficients.length];
			System.arraycopy(mCoefficients, 0, fixedCoefficients, 0, mCoefficients.length);

			if (mAnalysisType.wantsGuesses() && motzkinGuesses.length > 0) {
				// Convert Motzkin coefficients from Rationals into Terms
				final Term[] motzkinCoeffs = new Term[motzkinGuesses.length];
				for (int i = 0; i < motzkinGuesses.length; ++i) {
					motzkinCoeffs[i] = motzkinGuesses[i].toTerm(SmtSortUtils.getRealSort(mScript));
				}

				final int[] cases = new int[numfixedCoeffs]; // initialized to 0 by default
				final List<Term> disjunction = new ArrayList<>();
				if (numfixedCoeffs == 0) {
					disjunction.add(doTransform(fixedCoefficients, vars));
				} else {
					while (cases[numfixedCoeffs - 1] < motzkinGuesses.length) {
						if (!mServices.getProgressMonitorService().continueProcessing()) {
							throw new ToolchainCanceledException(this.getClass(),
									"approximative transformation where we make " + motzkinGuesses.length
											+ " guesses");
						}
						// Update the coefficients array
						for (int j = 0; j < numfixedCoeffs; ++j) {
							fixedCoefficients[fixedIndices[j]] = motzkinCoeffs[cases[j]];
						}
						disjunction.add(doTransform(fixedCoefficients, vars));
						// Increment the cases counter
						int i = 0;
						while (i < numfixedCoeffs) {
							++cases[i];
							if (i < numfixedCoeffs - 1 && cases[i] >= motzkinGuesses.length) {
								cases[i] = 0;
								++i;
							} else {
								break;
							}
						}
					}
				}
				conjunction.add(SmtUtils.or(mScript, disjunction.toArray(new Term[disjunction.size()])));
			} else {
				// Fixed values
				final Term zero = mScript.decimal("0");
				final Term one = mScript.decimal("1");

				final List<Term> disjunction = new ArrayList<>();
				for (int i = 0; i < (1 << numfixedCoeffs); ++i) {
					if (!mServices.getProgressMonitorService().continueProcessing()) {
						throw new ToolchainCanceledException(this.getClass(),
								"approximative transformation where we fixed " + (1 << numfixedCoeffs)
										+ " coefficients");
					}
					// Update the coefficients array
					for (int j = 0; j < numfixedCoeffs; ++j) {
						fixedCoefficients[fixedIndices[j]] = (i & (1 << j)) == 0 ? zero : one;
					}
					disjunction.add(doTransform(fixedCoefficients, vars));
				}
				conjunction.add(SmtUtils.or(mScript, disjunction.toArray(new Term[disjunction.size()])));
			}
		} else if (mAnalysisType == AnalysisType.NONLINEAR) {
			conjunction.add(doTransform(mCoefficients, vars));

			// Fixed Motzkin coefficients
			for (int i = 0; i < mInequalities.size(); ++i) {
				final LinearInequality li = mInequalities.get(i);
				if (li.mMotzkinCoefficient == PossibleMotzkinCoefficients.ZERO_AND_ONE) {
					// Fixing Motzkin coefficient to { 0, 1 }
					conjunction.add(SmtUtils.or(mScript, mScript.term("=", mCoefficients[i], mScript.decimal("0")),
							mScript.term("=", mCoefficients[i], mScript.decimal("1"))));
				}
			}
		} else {
			throw new AssertionError("Illegal enum value " + mAnalysisType);
		}
		Term t = SmtUtils.and(mScript, conjunction.toArray(new Term[conjunction.size()]));

		// Possibly annotate the term
		if (mAnnotateTerms && mAnnotation != null) {
			t = mScript.annotate(t, new Annotation(":named", mAnnotation.replace(" ", "_")));
		}
		return t;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("MotzkinApplication\n");
		if (mAnnotation != null) {
			sb.append("Annotation: ");
			sb.append(mAnnotation);
			sb.append("\n");
		}
		sb.append("Inequalities:");
		for (final LinearInequality li : mInequalities) {
			sb.append("\n    ");
			sb.append(li);
		}
		if (mTransformed) {
			sb.append("\nConstraints:\n");
			final boolean annotateTerms = mAnnotateTerms;
			mAnnotateTerms = false;
			sb.append(new SMTPrettyPrinter(transform(new Rational[0])));
			mAnnotateTerms = annotateTerms;
		}
		return sb.toString();
	}
}
