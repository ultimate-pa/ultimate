/*
 * Copyright (C) 2009-2022 University of Freiburg
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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * This class removes all let terms from the formula. It's a term transformer
 * that transforms a term with lets into an equivalent term without let.
 *
 * A tricky issue here are variable name clashes that can appear when renaming.
 * This class will check whether renaming is necessary, i.e., if a let makes a
 * variable with the same name as a bounded variable visible inside the
 * quantifier. A simple example is
 * {@code (let ((y x)) (exists ((x Int)) (= x y)))}. In this case the variable
 * of the inner quantifier is renamed by adding dots in front of it. Note that
 * symbols starting with a dot are reserved for solver use.
 *
 * By renaming in a consistent manner and by only renaming if there is a name
 * clash, the unletted form of an assumed term in a proof should be equal to the
 * unletted asserted term.
 *
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
		UnletType(final boolean lazy, final boolean expandDefinitions) {
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
			new ScopedHashMap<>(false);

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
	public FormulaUnLet(final UnletType type) {
		mType = type;
	}

	/**
	 * Add user defined substitutions.  This allows to map variables to
	 * terms, without adding a surrounding let term first.  Note that these
	 * substitutions are then used for all formulas unletted by this class.
	 * @param termSubst The substitution, which maps term variables to
	 * the term with which they should be substituted.
	 */
	public void addSubstitutions(final Map<TermVariable, Term> termSubst) {
		mLetMap.putAll(termSubst);
	}

	/**
	 * Unlet a term, i.e., remove all LetTerm and replace the term variables
	 * accordingly.
	 * @param term the term to unlet
	 * @return the resulting let-free term.
	 */
	public Term unlet(final Term term) {
		return transform(term);
	}

	private boolean isRenamedVar(String name) {
		// Renamed variables are of the form .[1-9][0-9]*.originalname.
		return name.charAt(0) == '.' && name.charAt(1) >= '1' && name.charAt(1) <= '9';
	}

	private void noteUsage(Map<String, Integer> usageMap, TermVariable usedTv) {
		/*
		 * we do bounded renaming on variables. For each variables x, we use the
		 * internal variables x, .1.x, .2.x, ... The generation is 0 for the original
		 * variable, otherwise it is the number after the r. We remember the maximum
		 * generation in usageMap, so that we rename every variable to the next
		 * generation after it.
		 */
		String name = usedTv.getName();
		int generation = 0;
		if (isRenamedVar(name)) {
			final int dotPos = name.indexOf('.', 2);
			generation = Integer.valueOf(name.substring(1, dotPos));
			name = name.substring(dotPos + 1);
		}
		final Integer oldGen = usageMap.put(name, generation);
		if (oldGen != null && oldGen > generation) {
			usageMap.put(name, oldGen);
		}
	}

	private String boundedRename(Map<String, Integer> usageMap, String name) {
		if (isRenamedVar(name)) {
			name = name.substring(name.indexOf('.', 2) + 1);
		}
		final Integer usedOutside = usageMap.get(name);
		if (usedOutside == null) {
			return name;
		} else {
			return "." + (usedOutside + 1) + "." + name;
		}
	}

	/**
	 * This is called for each quantifier, lambda term, or match term that
	 * introduces new bound variables. It determines if there is a name clash and
	 * renamed the bound variables accordingly. It adds the corresponding renaming
	 * to the let map.
	 *
	 * This also adds a new scope to the let map.
	 *
	 * @param body The term that contains the bounded variables.
	 * @param vars The bounded variables that may need to be renamed.
	 */
	public void startVarScope(final Term body, final TermVariable[] vars) {
		/* compute all variables that are indirectly used inside the body */
		final HashMap<String, Integer> usedOutside = new HashMap<>();
		final HashSet<TermVariable> bodyVars = new HashSet<>();
		bodyVars.addAll(Arrays.asList(body.getFreeVars()));
		for (final TermVariable tv : vars) {
			bodyVars.remove(tv);
		}
		for (final TermVariable tv : bodyVars) {
			final Term refTerm = mLetMap.get(tv);
			if (refTerm == null) {
				noteUsage(usedOutside, tv);
			} else {
				for (final TermVariable usedTv : refTerm.getFreeVars()) {
					noteUsage(usedOutside, usedTv);
				}
			}
		}

		mLetMap.beginScope();
		for (int i = 0; i < vars.length; i++) {
			final String name = vars[i].getName();
			final String newName = boundedRename(usedOutside, name);
			if (newName.equals(name)) {
				// remove the name from mLetMap so that it is kept.
				if (mLetMap.containsKey(vars[i])) {
					mLetMap.remove(vars[i]);
				}
			} else {
				// do bounded renaming.
				mLetMap.put(vars[i], vars[i].getTheory().createTermVariable(newName, vars[i].getSort()));
			}
		}
	}

	/**
	 * Ends a variable scope and determines the renamed bounded variables.
	 *
	 * @param vars the bounded variables of the exists, lambda or match term.
	 * @return the renamed variables in case renaming bounded variables were
	 *         necessary (returns vars if no renaming was necessary).
	 */
	public TermVariable[] endVarScope(final TermVariable[] vars) {
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
	public void convert(final Term term) {
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
		} else if (term instanceof LambdaTerm) {
			final LambdaTerm lambda = (LambdaTerm) term;
			startVarScope(lambda.getSubterm(), lambda.getVariables());
			super.convert(term);
		} else if (term instanceof QuantifiedFormula) {
			final QuantifiedFormula qf = (QuantifiedFormula)term;
			startVarScope(qf.getSubformula(), qf.getVariables());
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
	public void preConvertLet(final LetTerm oldLet, final Term[] newValues) {
		mLetMap.beginScope();
		final TermVariable[] vars = oldLet.getVariables();
		for (int i = 0; i < vars.length; i++) {
			mLetMap.put(vars[i], newValues[i]);
		}
		super.preConvertLet(oldLet, newValues);
	}

	@Override
	public void postConvertLet(final LetTerm oldLet, final Term[] newValues, final Term newBody) {
		setResult(newBody);
		mLetMap.endScope();
	}

	/**
	 * Build the converted formula for a lambda term. This also ends the scope of
	 * the lambda term. It stores the converted quantifier using
	 * {@link #setResult(Term)}.
	 *
	 * @param old     the quantifier to convert.
	 * @param newBody the converted sub formula.
	 */
	@Override
	public void postConvertLambda(final LambdaTerm old, final Term newBody) {
		final TermVariable[] vars = old.getVariables();
		final TermVariable[] newVars = endVarScope(vars);
		if (vars == newVars && old.getSubterm() == newBody) {
			setResult(old);
		} else {
			final Theory theory = old.getTheory();
			setResult(theory.lambda(newVars, newBody));
		}
	}

	/**
	 * Build the converted formula for a quantified formula. This also ends the
	 * scope of the quantifier. It stores the converted quantifier using
	 * {@link #setResult(Term)}.
	 *
	 * @param old     the quantifier to convert.
	 * @param newBody the converted sub formula.
	 */
	@Override
	public void postConvertQuantifier(final QuantifiedFormula old, final Term newBody) {
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
	public void preConvertMatchCase(final MatchTerm oldMatch, final int caseNr) {
		if (caseNr > 0) {
			mMatchVars.add(endVarScope(oldMatch.getVariables()[caseNr - 1]));
		}
		startVarScope(oldMatch.getCases()[caseNr], oldMatch.getVariables()[caseNr]);
		super.preConvertMatchCase(oldMatch, caseNr);
	}

	@Override
	public void postConvertMatch(final MatchTerm oldMatch, final Term newDataTerm, final Term[] newCases) {
		assert oldMatch.getCases().length > 0;
		mMatchVars.add(endVarScope(oldMatch.getVariables()[oldMatch.getVariables().length - 1]));
		final TermVariable[][] oldVars = oldMatch.getVariables();
		TermVariable[][] newVars = null;
		for (int i = oldVars.length - 1; i >= 0; i--) {
			final TermVariable[] newVarsCase = mMatchVars.remove(mMatchVars.size() - 1);
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
