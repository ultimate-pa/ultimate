/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Unifies transition formulas so that they refer to the same input/output variables using the same term variables, and
 * do not share any auxiliary variables. In order to preserve the semantics while adding output variables, explicit
 * equalities of input and output variables are generated.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class TransFormulaUnification {
	private final ManagedScript mMgdScript;
	private final UnmodifiableTransFormula[] mTransFormulas;
	private final Term[] mUnifiedFormulas;

	private final Map<IProgramVar, TermVariable> mInVars = new HashMap<>();
	private final Map<IProgramVar, TermVariable> mOutVars = new HashMap<>();
	private final Set<IProgramVar> mAssignedVars = new HashSet<>();
	private final List<Map<TermVariable, TermVariable>> mSubstitutions = new ArrayList<>();
	private final Set<TermVariable> mAuxVars = new HashSet<>();
	private final Set<IProgramConst> mNonTheoryConsts = new HashSet<>();

	/**
	 * Unify the given transition formulas.
	 *
	 * @param mgdScript
	 *            A script that is used to generate fresh names.
	 * @param transFormulas
	 *            The transition formulas to unify.
	 */
	public TransFormulaUnification(final ManagedScript mgdScript, final UnmodifiableTransFormula... transFormulas) {
		mMgdScript = mgdScript;
		mTransFormulas = transFormulas;
		mUnifiedFormulas = new Term[transFormulas.length];

		computeJointInOutVars();
		collectNonTheoryConsts();
		computeSubstitutions();
		computeUnifiedFormulas();
	}

	public Map<IProgramVar, TermVariable> getInVars() {
		return mInVars;
	}

	public Map<IProgramVar, TermVariable> getOutVars() {
		return mOutVars;
	}

	public Set<TermVariable> getAuxVars() {
		return mAuxVars;
	}

	public Set<IProgramConst> getNonTheoryConsts() {
		return mNonTheoryConsts;
	}

	/**
	 * Get the unified form of the i-th input transition formula.
	 *
	 * @param i
	 *            The index of the transition formula whose unified term shall be retrieved.
	 * @return The term for a unified transition formula
	 */
	public Term getUnifiedFormula(final int i) {
		return mUnifiedFormulas[i];
	}

	/**
	 * Get the unified form of the given input transition formula.
	 *
	 * @param tf
	 *            The transition formula whose unified term shall be retrieved. Must have been in the initial input to
	 *            the constructor.
	 * @return The term for a unified transition formula
	 */
	public Term getUnifiedFormula(final UnmodifiableTransFormula tf) {
		return getUnifiedFormula(Arrays.asList(mTransFormulas).indexOf(tf));
	}

	/**
	 * Compute the input variable and output variable maps that will be used by all unified transition formulas.
	 */
	private void computeJointInOutVars() {
		for (final UnmodifiableTransFormula tf : mTransFormulas) {
			for (final IProgramVar pv : tf.getInVars().keySet()) {
				if (!mInVars.containsKey(pv)) {
					addFreshTermVariable(mInVars, pv, "In");
				}
			}

			for (final Map.Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
				final IProgramVar pv = entry.getKey();

				// Variables which are assigned in some but not all branches must also occur as inVars.
				// We can omit this step in the special case where the variable is assigned in all branches.
				if (!mInVars.containsKey(pv) && !assignedInAll(pv)) {
					addFreshTermVariable(mInVars, pv, "In");
				}

				// Auxiliary step: Add all inVars as outVars. Some will be overwritten below.
				mOutVars.put(pv, mInVars.get(pv));
			}

			// Collect variables assigned in at least one branch.
			mAssignedVars.addAll(tf.getAssignedVars());
		}

		// Overwrite the outVars (making them different from the inVars), if assigned in at least one branch.
		for (final IProgramVar pv : mAssignedVars) {
			addFreshTermVariable(mOutVars, pv, "Out");
		}
	}

	private void collectNonTheoryConsts() {
		for (final UnmodifiableTransFormula tf : mTransFormulas) {
			mNonTheoryConsts.addAll(tf.getNonTheoryConsts());
		}
	}

	private void addFreshTermVariable(final Map<IProgramVar, TermVariable> varMap, final IProgramVar variable,
			final String suffix) {
		final String baseName = variable.getGloballyUniqueId() + "_" + suffix;
		final TermVariable termVar = mMgdScript.constructFreshTermVariable(baseName, variable.getSort());
		varMap.put(variable, termVar);
	}

	private void computeSubstitutions() {
		computeJointInOutVars();
		for (final UnmodifiableTransFormula tf : mTransFormulas) {
			mSubstitutions.add(computeSubstitution(tf));
		}
	}

	/**
	 * Compute the substitution that must be applied to a transition formula, such that it uses the unified term
	 * variables and does not share auxiliary variables with other transition formulae.
	 *
	 * @param tf
	 *            The transition formula whose substitution is computed
	 * @return The substitution mapping for term variables belonging to input, output or auxiliary variables.
	 */
	private Map<TermVariable, TermVariable> computeSubstitution(final UnmodifiableTransFormula tf) {
		final Map<TermVariable, TermVariable> substitutionMapping = new HashMap<>();

		// input variables
		for (final Map.Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			final TermVariable previous = substitutionMapping.put(entry.getValue(), mInVars.get(entry.getKey()));
			assert previous == null : "duplicate in-variable substitution: " + entry.getValue();
		}

		// output variables
		for (final Map.Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			final IProgramVar pv = entry.getKey();
			final TermVariable outVar = entry.getValue();

			final boolean isAssignedVar = tf.getInVars().get(pv) != outVar;
			if (isAssignedVar) {
				final TermVariable previous = substitutionMapping.put(outVar, mOutVars.get(pv));
				assert previous == null : "duplicate in/out-variable substitution: " + outVar;
			} else {
				// For variables that have an out-variable but are not assigned, there are two options: either they are
				// not assigned by any of our transition formulas, and hence the new in- and out-vars are equal. Or,
				// they are assigned by some other transition formula. In the latter case, we here prefer to substitute
				// the old out-variable by the new in-variable rather than the new out-variable (we generate an explicit
				// equality between the two new variables below).
				assert substitutionMapping.get(outVar) == mInVars.get(pv);
			}
		}

		// auxiliary variables
		for (final TermVariable oldAuxVar : tf.getAuxVars()) {
			final TermVariable newAuxVar = mMgdScript.constructFreshCopy(oldAuxVar);
			substitutionMapping.put(oldAuxVar, newAuxVar);
			mAuxVars.add(newAuxVar);
		}

		return substitutionMapping;
	}

	private void computeUnifiedFormulas() {
		for (int i = 0; i < mTransFormulas.length; ++i) {
			mUnifiedFormulas[i] = computeUnifiedFormula(mTransFormulas[i], mSubstitutions.get(i));
		}
	}

	/**
	 * Compute the actual term for the unified transition formula.
	 *
	 * @param tf
	 *            The original, not yet unified transition formula
	 * @param substitution
	 *            The substitution that must be applied
	 * @return A term for the unified transition formula.
	 */
	private Term computeUnifiedFormula(final UnmodifiableTransFormula tf,
			final Map<TermVariable, TermVariable> substitution) {
		final Term renamedFormula = Substitution.apply(mMgdScript, substitution, tf.getFormula());
		final Term equalities = generateExplicitEqualities(tf);
		return SmtUtils.and(mMgdScript.getScript(), renamedFormula, equalities);
	}

	/**
	 * Generate explicitly stated equalities between input and output variables, in case the output variable is not
	 * otherwise assigned.
	 *
	 * @param tf
	 *            The transition formula for which equalities shall be generated.
	 * @return A conjunction of equalities
	 */
	private Term generateExplicitEqualities(final UnmodifiableTransFormula tf) {
		final var assignedVars = tf.getAssignedVars();
		final List<Term> equalities = new ArrayList<>();
		for (final IProgramVar pv : mAssignedVars) {
			// If pv is not modified in tf (but in one of the other transition formulas), add explicit equality
			if (!assignedVars.contains(pv)) {
				final TermVariable termInVar = mInVars.get(pv);
				assert termInVar != null;

				final TermVariable termOutVar = mOutVars.get(pv);
				assert termOutVar != null;

				assert termInVar != termOutVar : "assigned variable needs different in/out-vars";
				equalities.add(SmtUtils.binaryEquality(mMgdScript.getScript(), termInVar, termOutVar));
			}
		}
		return SmtUtils.and(mMgdScript.getScript(), equalities);
	}

	private boolean assignedInAll(final IProgramVar bv) {
		for (final UnmodifiableTransFormula tf : mTransFormulas) {
			if (!tf.getAssignedVars().contains(bv)) {
				return false;
			}
		}
		return true;
	}
}
