package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.transformers;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.SubtreePosition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * Variant of {@link Substitution}. Also substitutes {@link Term}s by other Terms. However, the substituted Terms are
 * identified by their position in the formula. Thus the same Term may be substituted by different Terms when it occurs
 * more than once in the original formula (which is also a {@link Term}).
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class PositionAwareSubstitution extends PositionAwareTermTransformer {
	private final ScopedHashMap<SubtreePosition, Term> mScopedPositionSubstitutionMapping;
	private final ScopedHashMap<Term, Term> mScopedTermSubstitutionMapping;

	public PositionAwareSubstitution(final Script script,
			final Map<? extends SubtreePosition, ? extends Term> positionSubstitution,
			final Map<Term, Term> termSubstitution) {
		super();
		mScopedPositionSubstitutionMapping = new ScopedHashMap<>();
		mScopedPositionSubstitutionMapping.putAll(positionSubstitution);
		mScopedTermSubstitutionMapping = new ScopedHashMap<>();
		mScopedTermSubstitutionMapping.putAll(termSubstitution);
	}

	public PositionAwareSubstitution(final ManagedScript mgdScript,
			final Map<? extends SubtreePosition, ? extends Term> positionSubstitution,
			final Map<Term, Term> termSubstitution) {
		this(mgdScript.getScript(), positionSubstitution, termSubstitution);
	}

	public PositionAwareSubstitution(final Script script,
			final Map<? extends SubtreePosition, ? extends Term> positionBasedSubstitution) {
		this(script, positionBasedSubstitution, Collections.emptyMap());
	}


	public PositionAwareSubstitution(final ManagedScript mgdScript,
			final Map<? extends SubtreePosition, ? extends Term> positionBasedSubstitution) {
		this(mgdScript, positionBasedSubstitution, Collections.emptyMap());
	}

	@Override
	protected void convert(final Term term, final SubtreePosition pos) {
		if (mScopedPositionSubstitutionMapping.containsKey(pos)) {
			setResult(mScopedPositionSubstitutionMapping.get(pos));
		} else if (mScopedTermSubstitutionMapping.containsKey(term)) {
			setResult(mScopedTermSubstitutionMapping.get(term));
		} else {
			if (term instanceof QuantifiedFormula) {
				mScopedPositionSubstitutionMapping.beginScope();
				mScopedTermSubstitutionMapping.beginScope();
				throw new UnsupportedOperationException("quantified formulas are not yet supported by this class");
//				final QuantifiedFormula qFormula = (QuantifiedFormula) term;
//				removeQuantifiedVarContainingKeys(qFormula);
//				term = renameQuantifiedVarsThatOccurInValues(qFormula);
			} else if (term instanceof LetTerm) {
				throw new UnsupportedOperationException("LetTerm not supported");
			}
			super.convert(term, pos);
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
		final Set<TermVariable> toRename = DataStructureUtils.union(
				varsOccuringInValues(qFormula.getVariables(), mScopedPositionSubstitutionMapping),
				varsOccuringInValues(qFormula.getVariables(), mScopedTermSubstitutionMapping));
		throw new UnsupportedOperationException("quantified formulas are not yet supported by this class");
//		if (toRename.isEmpty()) {
//			return qFormula;
//		}
//		if (mMgdScript == null) {
//			throw new UnsupportedOperationException("Substitution in quantified formula such that substitute "
//					+ "containes quantified variable. This (rare) case is "
//					+ "only supported if you call substitution with fresh " + "variable construction.");
//		}
//		final Term result = SmtUtils.renameQuantifiedVariables(mMgdScript, qFormula, toRename, "subst");
//		return result;
	}

	/**
	 * Remove from (current scope of) substitution mapping all substitutions where the key contains a variables that is
	 * quantified in this scope.
	 *
	 */
	private void removeQuantifiedVarContainingKeys(final QuantifiedFormula qFormula) {
		throw new UnsupportedOperationException("quantified formulas are not yet supported by this class");

//		final Iterator<Entry<SubtreePosition, Term>> it = mScopedPositionSubstitutionMapping.entrySet().iterator();
//		while (it.hasNext()) {
//			final Entry<SubtreePosition, Term> entry = it.next();
//			final List<TermVariable> quantifiedVars = Arrays.asList(qFormula.getVariables());
//			final List<TermVariable> occuringVars = Arrays.asList(entry.getKey().getFreeVars());
//			if (!Collections.disjoint(quantifiedVars, occuringVars)) {
//				it.remove();
//			}
//		}
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
		throw new UnsupportedOperationException("quantified formulas are not yet supported by this class");
//		Term result;
//		// to avoid capturing of variables we had to rename quantified vars
//		// to fresh vars in subterms. Now we have to construct the appropriate
//		// supterterm.
//		// How can we detect if a variable was renamed?
//		// If a variable (of the old superterm) was renamed, it is a key in the
//		// current substitution mapping.
//		TermVariable[] newQuantifiedVars = new TermVariable[old.getVariables().length];
//		boolean quantifiedVariablesChanged = false;
//		for (int i = 0; i < old.getVariables().length; i++) {
//			if (mScopedPositionSubstitutionMapping.containsKey(old.getVariables()[i])) {
//				newQuantifiedVars[i] = old.getVariables()[i];
//				quantifiedVariablesChanged = true;
//			} else {
//				newQuantifiedVars[i] = old.getVariables()[i];
//			}
//		}
//		if (old.getSubformula() == newBody) {
//			assert !quantifiedVariablesChanged;
//			result = old;
//		} else {
//			if (!quantifiedVariablesChanged) {
//				// reuse old array
//				newQuantifiedVars = old.getVariables();
//			}
//			result = mScript.quantifier(old.getQuantifier(), newQuantifiedVars, newBody);
//		}
//		mScopedPositionSubstitutionMapping.endScope();
//		setResult(result);
	}

	@Override
	public String toString() {
		return "Substitution " + mScopedPositionSubstitutionMapping.toString();
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
