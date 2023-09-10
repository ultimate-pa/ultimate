/*
 * Copyright (C) 2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * While considering a subformula φ of a formula. The <i>context</i> provides
 * some information about siblings and ancestors of φ. The <i>critical
 * constraint</i> is explained in "Small Formulas for Large Programms: On-Line
 * Constraint Simplification in Scalable Static Analysis" by Isil Dillig, Thomas
 * Dillig and Alex Aiken.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class Context {
	private static final CcTransformation OPTION_CCTRANSFORMATION = CcTransformation.OVERAPPROXIMATE_QUANTIFIERS;

	/**
	 * Transformations that can be done with the critical constraint.
	 *
	 */
	public enum CcTransformation {
		NONE,
		/**
		 * Bring negated siblings in for critical constraint in NNF. Allows us in some
		 * cases to get a smaller result. Comes with small additional consts because of
		 * the NNF transformation.
		 */
		TO_NNF,
		/**
		 * Bring siblings to NNF and replace all quantified formulas by true.
		 */
		OVERAPPROXIMATE_QUANTIFIERS };

	private final Term mCriticalConstraint;
	private final CcTransformation mCcTransformation;
	/**
	 * Contains the variables that are bound in {@link QuantifiedFormula}s that are
	 * ancestors of this context's subformula.
	 */
	private final Set<TermVariable> mBoundByAncestors;

	public Context(final Script script) {
		super();
		mCcTransformation = OPTION_CCTRANSFORMATION;
		mCriticalConstraint = script.term("true");
		mBoundByAncestors = Collections.emptySet();
	}

	public Context(final Term criticalConstraint, final Set<TermVariable> boundByAncestors) {
		super();
		mCcTransformation = OPTION_CCTRANSFORMATION;
		Objects.requireNonNull(criticalConstraint);
		Objects.requireNonNull(boundByAncestors);
		mCriticalConstraint = criticalConstraint;
		mBoundByAncestors = boundByAncestors;
	}

	public Term getCriticalConstraint() {
		return mCriticalConstraint;
	}

	public Set<TermVariable> getBoundByAncestors() {
		return Collections.unmodifiableSet(mBoundByAncestors);
	}

	public Context constructChildContextForQuantifiedFormula(final Script script,
			final List<TermVariable> quantifiedVars) {
		{
			// Throw UnsupportedOperationException if there are different variables with same name.
			final Set<TermVariable> all = Stream
					.concat(Arrays.asList(mCriticalConstraint.getFreeVars()).stream(), quantifiedVars.stream())
					.collect(Collectors.toSet());
			final String nameOfTwoDifferentVars = checkForDifferentVariablesWithSameName(all);
			if (nameOfTwoDifferentVars != null) {
				throw new UnsupportedOperationException(
						"Different variables with same name: " + nameOfTwoDifferentVars);
			}
		}
		final Term criticalConstraint = buildCriticalContraintForQuantifiedFormula(script, mCriticalConstraint,
				quantifiedVars, mCcTransformation);
		final Set<TermVariable> boundByAncestors = new HashSet<>(mBoundByAncestors);
		boundByAncestors.addAll(quantifiedVars);
		return new Context(criticalConstraint, boundByAncestors);
	}

	public Context constructChildContextForConDis(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final FunctionSymbol symb,
			final List<Term> allParams, final int selectedParam) {
		final Term criticalConstraint = buildCriticalConstraintForConDis(services, mgdScript, mCriticalConstraint, symb,
				allParams, selectedParam, mCcTransformation);
		return new Context(criticalConstraint, mBoundByAncestors);
	}

	public Context constructChildContextForConDis(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final FunctionSymbol symb,
			final List<Term> otherParams) {
		final Term criticalConstraint = buildCriticalConstraintForConDis(services, mgdScript, mCriticalConstraint, symb,
				otherParams, mCcTransformation);
		return new Context(criticalConstraint, mBoundByAncestors);
	}

	public static Term buildCriticalContraintForQuantifiedFormula(final Script script,
			final Term parentCriticalConstraint, final List<TermVariable> boundVars,
			final CcTransformation ccTransformation) {
		final Term quantified = SmtUtils.quantifier(script, QuantifiedFormula.EXISTS, boundVars,
				parentCriticalConstraint);
		final Term result;
		if (ccTransformation == CcTransformation.OVERAPPROXIMATE_QUANTIFIERS) {
			result = QuantifierOverapproximator.apply(script, quantified);
		} else {
			result = quantified;
		}
		return result;
	}

	/**
	 * Keep only the conjuncts of the parentCriticalConstraint that do not contain
	 * any of the bound variables. We assume that the parentCriticalConstraint is a
	 * conjunction of atoms.
	 */
	public static Term buildConjunctiveCriticalContraintForQuantifiedFormula(final Script script,
			final Term parentCriticalConstraint, final List<TermVariable> boundVars) {
		final Term[] conjuncts = SmtUtils.getConjuncts(parentCriticalConstraint);
		final List<Term> resultConjuncts = new ArrayList<>();
		for (final Term conjunct : conjuncts) {
			assert SmtUtils.isAtomicFormula(conjunct) : "non-atom in critical constraint";
			if (!Arrays.stream(conjunct.getFreeVars()).anyMatch(boundVars::contains)) {
				resultConjuncts.add(conjunct);
			}
		}
		return SmtUtils.and(script, resultConjuncts);
	}

	public static Term buildCriticalConstraintForConDis(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final Term parentCriticalConstraint, final FunctionSymbol symb,
			final List<Term> allParams, final int selectedParam, final CcTransformation ccTransformation) {
		final List<Term> otherParams = new ArrayList<>(allParams);
		otherParams.remove(selectedParam);
		return  buildCriticalConstraintForConDis(services, mgdScript, parentCriticalConstraint, symb,
				otherParams, ccTransformation);
	}

	private static Term buildCriticalConstraintForConDis(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final Term parentCriticalConstraint, final FunctionSymbol symb,
			final List<Term> otherParams, final CcTransformation ccTransformation) {
		final Term tmp;
		if (symb.getName().equals("and")) {
			tmp = SmtUtils.and(mgdScript.getScript(), otherParams);
		} else if (symb.getName().equals("or")) {
			final List<Term> otherParamsNegated;
			switch (ccTransformation) {
			case NONE:
				otherParamsNegated = otherParams.stream().map(x -> SmtUtils.not(mgdScript.getScript(), x))
						.collect(Collectors.toList());
				break;
			case OVERAPPROXIMATE_QUANTIFIERS:
			case TO_NNF:
				otherParamsNegated = otherParams.stream()
						.map(x -> new NnfTransformer(mgdScript, services, QuantifierHandling.KEEP)
								.transform(SmtUtils.not(mgdScript.getScript(), x)))
						.collect(Collectors.toList());
				break;
			default:
				throw new AssertionError("unknown value " + ccTransformation);

			}
			tmp = SmtUtils.and(mgdScript.getScript(), otherParamsNegated);
		} else if (symb.getName().equals("=")) {
			// TODO 20210516 Matthias: Decide whether we really want to support non-NNF
			// terms here.
			tmp = mgdScript.getScript().term("true");
		} else {
			throw new AssertionError("Supported: conjunction and disjunction. Got: " + symb);
		}
		final Term tmpWithParent = SmtUtils.and(mgdScript.getScript(), tmp, parentCriticalConstraint);
		final Term result;
		if (ccTransformation == CcTransformation.OVERAPPROXIMATE_QUANTIFIERS) {
			result = QuantifierOverapproximator.apply(mgdScript.getScript(), tmpWithParent);
		} else {
			result = tmpWithParent;
		}
		return result;
	}

	public static Term buildConjunctiveCriticalConstraintForConDis(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final Term parentCriticalConstraint, final FunctionSymbol symb,
			final List<Term> allParams, final int selectedParam) {
		final List<Term> otherParams = new ArrayList<>(allParams);
		otherParams.remove(selectedParam);
		return buildConjunctiveCriticalConstraintForConDis(services, mgdScript, parentCriticalConstraint, symb,
				otherParams);
	}

	private static Term buildConjunctiveCriticalConstraintForConDis(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final Term parentCriticalConstraint, final FunctionSymbol symb,
			final List<Term> otherParams) {
		Term result;
		if (symb.getName().equals("and")) {
			result = SmtUtils.and(mgdScript.getScript(),
					otherParams.stream().filter(SmtUtils::isAtomicFormula).collect(Collectors.toList()));
		} else if (symb.getName().equals("or")) {
			final List<Term> otherParamsNegated = otherParams.stream().filter(SmtUtils::isAtomicFormula)
					.map(x -> new NnfTransformer(mgdScript, services, QuantifierHandling.KEEP)
							.transform(SmtUtils.not(mgdScript.getScript(), x)))
					.collect(Collectors.toList());
			result = SmtUtils.and(mgdScript.getScript(), otherParamsNegated);
		} else if (symb.getName().equals("=")) {
			// TODO 20210516 Matthias: Decide whether we really want to support non-NNF
			// terms here.
			result = mgdScript.getScript().term("true");
		} else {
			throw new AssertionError("only conjunction and disjunction are supported");
		}
		result = SmtUtils.and(mgdScript.getScript(), result, parentCriticalConstraint);
		return result;
	}

	/**
	 * Return null if all variables have different names. Otherwise, return a name
	 * that occurs in several TermVariables.
	 */
	public String checkForDifferentVariablesWithSameName(final Collection<TermVariable> termVariables) {
		final Map<String, TermVariable> map = new HashMap<>();
		for (final TermVariable tv : termVariables) {
			final TermVariable old = map.put(tv.getName(), tv);
			if (old != null && !old.equals(tv)) {
				return old.getName();
			}
		}
		return null;
	}

}