/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * Substitution that replaces subterms by terms. Takes care the quantified variables are renamed to fresh variables such
 * that - no variable in substituted term is "captured" by an existing quantifier - no subterm that contains a bound
 * variable is substituted.
 *
 * Idea of this implementation. Replace quantified variables by fresh variables whenever a variable interferes with a
 * variable in the substitution mapping. TODO: If quantified variable occurs in key of substitution mapping, do not
 * rename quantified variable but remove substitution in the current scope.
 *
 * @author Matthias Heizmann
 */
public class Substitution extends TermTransformer {

	private final Script mScript;
	protected final ManagedScript mMgdScript;
	private final ScopedHashMap<Term, Term> mScopedSubstitutionMapping;

	public Substitution(final Script script, final Map<? extends Term, ? extends Term> substitutionMapping) {
		super();
		mMgdScript = null;
		mScript = script;
		mScopedSubstitutionMapping = new ScopedHashMap<>();
		mScopedSubstitutionMapping.putAll(substitutionMapping);
	}

	public Substitution(final ManagedScript mgdScript, final Map<? extends Term, ? extends Term> substitutionMapping) {
		super();
		mMgdScript = mgdScript;
		mScript = mgdScript.getScript();
		mScopedSubstitutionMapping = new ScopedHashMap<>();
		mScopedSubstitutionMapping.putAll(substitutionMapping);
	}

	@Override
	protected void convert(Term term) {
		final Term mappedTerm = mScopedSubstitutionMapping.get(term);
		if (mappedTerm != null) {
			setResult(mappedTerm);
		} else {
			if (term instanceof QuantifiedFormula) {
				mScopedSubstitutionMapping.beginScope();
				final QuantifiedFormula qFormula = (QuantifiedFormula) term;
				removeQuantifiedVarContainingKeys(qFormula);
				term = renameQuantifiedVarsThatOccurInValues(qFormula);
			} else if (term instanceof LetTerm) {
				throw new UnsupportedOperationException("LetTerm not supported");
			}
			super.convert(term);
		}
	}

	/**
	 * Rename all quantified variables (in the current scope) that occur in values of the substitution mapping (of the
	 * current scope). We use fresh names that never occurred before. This avoids that after the substitution a
	 * variables in a substituted subterm is "accidently" captured by a quantifier.
	 *
	 * @return
	 */
	private Term renameQuantifiedVarsThatOccurInValues(final QuantifiedFormula qFormula) {
		final Set<TermVariable> toRename = varsOccuringInValues(qFormula.getVariables(), mScopedSubstitutionMapping);
		if (toRename.isEmpty()) {
			return qFormula;
		}
		if (mMgdScript == null) {
			throw new UnsupportedOperationException("Substitution in quantified formula such that substitute "
					+ "containes quantified variable. This (rare) case is "
					+ "only supported if you call substitution with fresh " + "variable construction.");
		}
		final Term result = SmtUtils.renameQuantifiedVariables(mMgdScript, qFormula, toRename, "subst");
		return result;

	}

	/**
	 * Remove from (current scope of) substitution mapping all substitutions where the key contains a variables that is
	 * quantified in this scope.
	 *
	 */
	private void removeQuantifiedVarContainingKeys(final QuantifiedFormula qFormula) {

		final Iterator<Entry<Term, Term>> it = mScopedSubstitutionMapping.entrySet().iterator();
		while (it.hasNext()) {
			final Entry<Term, Term> entry = it.next();
			final List<TermVariable> quantifiedVars = Arrays.asList(qFormula.getVariables());
			final List<TermVariable> occuringVars = Arrays.asList(entry.getKey().getFreeVars());
			if (!Collections.disjoint(quantifiedVars, occuringVars)) {
				it.remove();
			}
		}
	}

	/**
	 * Returns the subset of vars that occur as free variables in the values of map.
	 */
	private static Set<TermVariable> varsOccuringInValues(final TermVariable vars[], final Map<?, Term> map) {
		Set<TermVariable> result = null;
		for (final Term term : map.values()) {
			for (final TermVariable tv : term.getFreeVars()) {
				if (Arrays.asList(vars).contains(tv)) {
					result = addToSet(tv, result);
				}
			}
		}
		if (result == null) {
			result = Collections.emptySet();
		}
		return result;
	}

	/**
	 * Add tv to set and return set. Construct HashSet if set is null.
	 */
	private static Set<TermVariable> addToSet(final TermVariable tv, Set<TermVariable> set) {
		if (set == null) {
			set = new HashSet<>();
		}
		set.add(tv);
		return set;
	}

	@Override
	public void postConvertQuantifier(final QuantifiedFormula old, final Term newBody) {
		Term result;
		// to avoid capturing of variables we had to rename quantified vars
		// to fresh vars in subterms. Now we have to construct the appropriate
		// supterterm.
		// How can we detect if a variable was renamed?
		// If a variable (of the old superterm) was renamed, it is a key in the
		// current substitution mapping.
		TermVariable[] newQuantifiedVars = new TermVariable[old.getVariables().length];
		boolean quantifiedVariablesChanged = false;
		for (int i = 0; i < old.getVariables().length; i++) {
			if (mScopedSubstitutionMapping.containsKey(old.getVariables()[i])) {
				newQuantifiedVars[i] = old.getVariables()[i];
				quantifiedVariablesChanged = true;
			} else {
				newQuantifiedVars[i] = old.getVariables()[i];
			}
		}
		if (old.getSubformula() == newBody) {
			assert !quantifiedVariablesChanged;
			result = old;
		} else {
			if (!quantifiedVariablesChanged) {
				// reuse old array
				newQuantifiedVars = old.getVariables();
			}
			result = mScript.quantifier(old.getQuantifier(), newQuantifiedVars, newBody);
		}
		mScopedSubstitutionMapping.endScope();
		setResult(result);
	}

	@Override
	public String toString() {
		return "Substitution " + mScopedSubstitutionMapping.toString();
	}

	/**
	 * Apply substitution to each Term in a List.
	 *
	 * @return A new List that contains (in the same order) the results of the substitutions applied to each input Term.
	 */
	public List<Term> transform(final List<Term> terms) {
		final ArrayList<Term> result = new ArrayList<>();
		for (final Term term : terms) {
			result.add(this.transform(term));
		}
		return result;
	}

}
