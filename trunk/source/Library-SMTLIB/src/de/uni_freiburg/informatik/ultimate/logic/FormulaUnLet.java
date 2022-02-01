/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.logic;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * This class removes all let terms from the formula.  The result
 * @author Jochen Hoenicke
 */
public class FormulaUnLet extends TermTransformer {

	public enum UnletType {
		/**
		 * The SMTLIB compliant unlet that does not expand definitions.
		 */
		SMTLIB(false, false),
		/**
		 * The non-SMTLIB compliant unlet that does not expand definitions but
		 * uses the lazy semantics.
		 */
		LAZY(true, false),
		/**
		 * The SMTLIB compliant unlet that expands definitions.
		 */
		EXPAND_DEFINITIONS(false, true);
		/**
		 * True for lazy let semantics.  The normal semantics of SMTLIB is
		 * non-lazy, i.e. the values of a let are evaluated before they are
		 * assigned to the corresponding variable.  With lazy let, the value is
		 * expanded only when the variable is used later.  This was useful once
		 * for interpolation.
		 */
		final boolean mIsLazy;
		/**
		 * Should defined functions be expanded.  Defaults to false.
		 */
		final boolean mExpandDefinitions;
		UnletType(boolean lazy, boolean expandDefinitions) {
			mIsLazy = lazy;
			mExpandDefinitions = expandDefinitions;
		}
	}

	/**
	 * The scoped let map. Each scope corresponds to a partially executed let
	 * or a quantifier on the todo stack.  It gives the mapping for each
	 * term variable defined in that scope to the corresponding term.
	 */
	private final ScopedHashMap<TermVariable,Term> mLetMap =
			new ScopedHashMap<TermVariable, Term>(false);

	/**
	 * The type of this unletter.
	 */
	private final UnletType mType;

	/**
	 * The converted match variable arrays.
	 */
	private final ArrayList<TermVariable[]> mMatchVars = new ArrayList<>();

	/**
	 * Create a FormulaUnLet with the standard SMT-LIB semantics for let.
	 */
	public FormulaUnLet() {
		this(UnletType.SMTLIB);
	}

	/**
	 * Create a FormulaUnLet.
	 * @param type  The type of the unletter.
	 */
	public FormulaUnLet(UnletType type) {
		mType = type;
	}

	/**
	 * Add user defined substitutions.  This allows to map variables to
	 * terms, without adding a surrounding let term first.  Note that these
	 * substitutions are then used for all formulas unletted by this class.
	 * @param termSubst The substitution, which maps term variables to
	 * the term with which they should be substituted.
	 */
	public void addSubstitutions(Map<TermVariable, Term> termSubst) {
		mLetMap.putAll(termSubst);
	}

	/**
	 * Unlet a term, i.e., remove all LetTerm and replace the term variables
	 * accordingly.
	 * @param term the term to unlet
	 * @return the resulting let-free term.
	 */
	public Term unlet(Term term) {
		return transform(term);
	}

	public void startVarScope(TermVariable[] vars) {
		/* check which variables are in the image of the substitution */
		final HashSet<TermVariable> used = new HashSet<TermVariable>();
		for (final Map.Entry<TermVariable, Term> substTerms : mLetMap.entrySet()) {
			if (!Arrays.asList(vars).contains(substTerms.getKey())) {
				used.addAll(Arrays.asList(substTerms.getValue().getFreeVars()));
			}
		}

		mLetMap.beginScope();
		for (int i = 0; i < vars.length; i++) {
			if (used.contains(vars[i])) {
				mLetMap.put(vars[i], vars[i].getTheory().createFreshTermVariable("unlet", vars[i].getSort()));
			} else {
				if (mLetMap.containsKey(vars[i])) {
					mLetMap.remove(vars[i]);
				}
			}
		}
	}

	public TermVariable[] endVarScope(TermVariable[] vars) {
		TermVariable[] newVars = vars;
		for (int i = 0; i < vars.length; i++) {
			final Term newVar = mLetMap.get(vars[i]);
			if (newVar != null) {
				if (vars == newVars) {
					newVars = vars.clone();
				}
				newVars[i] = (TermVariable) newVar;
			}
		}
		mLetMap.endScope();
		return newVars;
	}

	@Override
	public void convert(Term term) {
		if (term instanceof TermVariable) {
			final Term value = mLetMap.get(term);
			if (value == null) {
				setResult(term);
			} else if (mType.mIsLazy) {
				pushTerm(value);
			} else {
				setResult(value);
			}
		} else if (mType.mIsLazy && term instanceof LetTerm) {
			final LetTerm letTerm = (LetTerm) term;
			preConvertLet(letTerm, letTerm.getValues());
		} else if (term instanceof QuantifiedFormula) {
			final QuantifiedFormula qf = (QuantifiedFormula)term;
			startVarScope(qf.getVariables());
			super.convert(term);
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if (mType.mExpandDefinitions
					&& appTerm.getFunction().getDefinition() != null) {
				final FunctionSymbol defed = appTerm.getFunction();
				final Term fakeLet = appTerm.getTheory().let(
						defed.getDefinitionVars(), appTerm.getParameters(),
						defed.getDefinition());
				pushTerm(fakeLet);
				return;
			}
			super.convert(term);
		} else {
			super.convert(term);
		}
	}

	@Override
	public void preConvertLet(LetTerm oldLet, Term[] newValues) {
		mLetMap.beginScope();
		final TermVariable[] vars = oldLet.getVariables();
		for (int i = 0; i < vars.length; i++) {
			mLetMap.put(vars[i], newValues[i]);
		}
		super.preConvertLet(oldLet, newValues);
	}

	@Override
	public void postConvertLet(LetTerm oldLet, Term[] newValues, Term newBody) {
		setResult(newBody);
		mLetMap.endScope();
	}

	/**
	 * Build the converted formula for a quantified formula.
	 * This also ends the scope of the quantifier.
	 * It stores the converted quantifier using {@link #setResult(Term)}.
	 * @param old the quantifier to convert.
	 * @param newBody the converted sub formula.
	 */
	@Override
	public void postConvertQuantifier(QuantifiedFormula old, Term newBody) {
		final TermVariable[] vars = old.getVariables();
		final TermVariable[] newVars = endVarScope(vars);
		if (vars == newVars && old.getSubformula() == newBody) {
			setResult(old);
		} else {
			final Theory theory = old.getTheory();
			setResult(old.getQuantifier() == QuantifiedFormula.EXISTS
					? theory.exists(newVars, newBody)
					: theory.forall(newVars, newBody));
		}
	}

	@Override
	public void preConvertMatchCase(MatchTerm oldMatch, int caseNr) {
		if (caseNr > 0) {
			mMatchVars.add(endVarScope(oldMatch.getVariables()[caseNr - 1]));
		}
		startVarScope(oldMatch.getVariables()[caseNr]);
		super.preConvertMatchCase(oldMatch, caseNr);
	}

	@Override
	public void postConvertMatch(MatchTerm oldMatch, Term newDataTerm, Term[] newCases) {
		assert oldMatch.getCases().length > 0;
		mMatchVars.add(endVarScope(oldMatch.getVariables()[oldMatch.getVariables().length - 1]));
		TermVariable[][] oldVars = oldMatch.getVariables();
		TermVariable[][] newVars = null;
		for (int i = oldVars.length - 1; i >= 0; i--) {
			TermVariable[] newVarsCase = mMatchVars.remove(mMatchVars.size() - 1);
			if (newVarsCase != oldVars[i]) {
				if (newVars == null) {
					newVars = oldVars.clone();
				}
				newVars[i] = newVarsCase;
			}
		}
		if (newVars != null) {
			setResult(oldMatch.getTheory().match(newDataTerm, newVars, newCases, oldMatch.getConstructors()));
		} else {
			super.postConvertMatch(oldMatch, newDataTerm, newCases);
		}
	}
}
