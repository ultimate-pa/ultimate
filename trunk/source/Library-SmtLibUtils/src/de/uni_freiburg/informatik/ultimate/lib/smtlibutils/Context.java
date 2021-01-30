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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * While considering a subformula φ of a formula. The <i>context</i> provides
 * some information about siblings and ancestors of φ. The <i>context</i>
 * consists of a <i>critical constraint</i> and a set of variables called
 * <i>bound in context</i>. The critical constraint is explained in "Small
 * Formulas for Large Programms: On-Line Constraint Simplification in Scalable
 * Static Analysis" by Isil Dillig, Thomas Dillig and Alex Aiken.
 * The bound-in-context variables contains all variables that are bound
 * in {@link QuantifiedFormula}s that are ancestors of φ.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class Context {
	private final Term mCriticalConstraint;
	private final Set<TermVariable> mBoundInContext;

	public Context(final Script script) {
		super();
		mCriticalConstraint = script.term("true");
		mBoundInContext = Collections.emptySet();
	}

	public Context(final Term criticalConstraint, final Set<TermVariable> boundInContext) {
		super();
		Objects.requireNonNull(criticalConstraint);
		Objects.requireNonNull(boundInContext);
		mCriticalConstraint = criticalConstraint;
		mBoundInContext = boundInContext;
	}
	public Term getCriticalConstraint() {
		return mCriticalConstraint;
	}
	public Set<TermVariable> getBoundInContext() {
		return Collections.unmodifiableSet(mBoundInContext);
	}

	public static Term buildCriticalContraintForQuantifiedFormula(final Script script, final Term context,
			final List<TermVariable> boundVars) {
		return SmtUtils.quantifier(script, QuantifiedFormula.EXISTS, boundVars, context);
	}

	public static Term buildCriticalConstraintForConDis(final Script script, final Term parentContext,
			final FunctionSymbol symb, final List<Term> allParams, final int selectedParam) {
		final List<Term> otherParams = new ArrayList<>(allParams);
		otherParams.remove(selectedParam);
		return buildCriticalConstraintForConDis(script, parentContext, symb, otherParams);
	}

	public static Term buildCriticalConstraintForConDis(final Script script, final Term parentContext,
			final FunctionSymbol symb, final List<Term> otherParams) {
		Term result;
		if (symb.getName().equals("and")) {
			result = SmtUtils.and(script, otherParams);
		} else if (symb.getName().equals("or")) {
			final List<Term> otherParamsNegated = otherParams.stream().map(x -> SmtUtils.not(script, x))
					.collect(Collectors.toList());
			result = SmtUtils.and(script, otherParamsNegated);
		} else {
			throw new AssertionError("only conjunction and disjunction are supported");
		}
		result = SmtUtils.and(script, result, parentContext);
		return result;
	}



}