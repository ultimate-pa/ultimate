/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IcfgTransformer library.
 * 
 * The ULTIMATE IcfgTransformer library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IcfgTransformer library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.IReplacementVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.IReplacementVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Abstract superclass for preprocessors that replace TermVariables. Note that we have already removed constants 0-ary
 * functions, hence we only have to remove TermVariables
 * 
 * @author Matthias Heizmann
 *
 */
public abstract class RewriteTermVariables extends TransitionPreprocessor {

	/**
	 * Maps TermVariable that have to replaced to the term by which they are replaced.
	 */
	private final Map<Term, Term> mSubstitutionMapping;

	/**
	 * Factory for construction of auxVars.
	 */
	private final ReplacementVarFactory mVarFactory;
	protected final ManagedScript mScript;

	/**
	 * The sort to be used for new replacement TermVariable's
	 */
	private final Sort mRepVarSort;

	public RewriteTermVariables(final ReplacementVarFactory varFactory, final ManagedScript script) {
		mVarFactory = varFactory;
		mScript = script;
		mRepVarSort = mScript.getScript().sort(getRepVarSortName());
		mSubstitutionMapping = new LinkedHashMap<>();
	}

	/**
	 * Compute definition (see {@link IProgramVar#getDefinition()} for RankVar that will replace oldRankVar.
	 */
	protected abstract Term constructNewDefinitionForRankVar(IProgramVar oldRankVar);

	/**
	 * Construct the Term that will replace the old TermVariable for which we already constructed the new TermVariable
	 * newTv.
	 */
	protected abstract Term constructReplacementTerm(TermVariable newTv);

	/**
	 * @return true iff term will be replaced by this preprocessor
	 */
	protected abstract boolean hasToBeReplaced(Term term);

	/**
	 * @return name of the Sort that we use for the new variables. This has to be either "Int" or "Real".
	 */
	protected abstract String getRepVarSortName();

	/**
	 * @return the suffix that the new TermVariables get. This is mainly important for debugging purposes that we can
	 *         see that this preprocessor indeed constructed the variable.
	 */
	protected abstract String getTermVariableSuffix();

	/**
	 * Get the new ReplacementVar for a given RankVar. Constructs a new replacement variable, if needed.
	 */
	private final IReplacementVarOrConst getOrConstructReplacementVar(final IProgramVar rankVar) {
		final Term definition = constructNewDefinitionForRankVar(rankVar);
		final IReplacementVar repVar = (IReplacementVar) mVarFactory.getOrConstuctReplacementVar(definition, false);
		return repVar;
	}

	/**
	 * Traverse all inVars, outVars and outVars and construct the new ReplacementVars and replacing Terms (and put them
	 * into the substitution mapping).
	 */
	private final void generateRepAndAuxVars(final ModifiableTransFormula tf) {
		final ArrayList<IProgramVar> rankVarsWithDistinctInVar = new ArrayList<>();
		final ArrayList<IProgramVar> rankVarsWithDistinctOutVar = new ArrayList<>();
		final ArrayList<IProgramVar> rankVarsWithCommonInVarOutVar = new ArrayList<>();
		for (final Map.Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			if (hasToBeReplaced(entry.getValue())) {
				if (ModifiableTransFormulaUtils.inVarAndOutVarCoincide(entry.getKey(), tf)) {
					rankVarsWithCommonInVarOutVar.add(entry.getKey());
				} else {
					rankVarsWithDistinctInVar.add(entry.getKey());
				}
			}
		}
		for (final Map.Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			if (hasToBeReplaced(entry.getValue())) {
				if (ModifiableTransFormulaUtils.inVarAndOutVarCoincide(entry.getKey(), tf)) {
					// do nothing, was already added
				} else {
					rankVarsWithDistinctOutVar.add(entry.getKey());
				}
			}
		}

		for (final IProgramVar rv : rankVarsWithCommonInVarOutVar) {
			final IReplacementVarOrConst varOrConst = getOrConstructReplacementVar(rv);
			if (varOrConst instanceof ReplacementConst) {
				throw new UnsupportedOperationException("not yet implemented");
			}
			final IReplacementVar repVar = (IReplacementVar) varOrConst;
			final TermVariable newInOutVar = mVarFactory.getOrConstructAuxVar(
					computeTermVariableName(repVar.getGloballyUniqueId(), true, true), mRepVarSort);
			final Term replacementTerm = constructReplacementTerm(newInOutVar);
			mSubstitutionMapping.put(tf.getInVars().get(rv), replacementTerm);
			tf.removeInVar(rv);
			tf.addInVar(repVar, newInOutVar);
			tf.removeOutVar(rv);
			tf.addOutVar(repVar, newInOutVar);
		}

		for (final IProgramVar rv : rankVarsWithDistinctInVar) {
			final IReplacementVarOrConst varOrConst = getOrConstructReplacementVar(rv);
			if (varOrConst instanceof ReplacementConst) {
				throw new UnsupportedOperationException("not yet implemented");
			}
			final IReplacementVar repVar = (IReplacementVar) varOrConst;
			final TermVariable newInVar = mVarFactory.getOrConstructAuxVar(
					computeTermVariableName(repVar.getGloballyUniqueId(), true, false), mRepVarSort);
			final Term replacementTerm = constructReplacementTerm(newInVar);
			mSubstitutionMapping.put(tf.getInVars().get(rv), replacementTerm);
			tf.removeInVar(rv);
			tf.addInVar(repVar, newInVar);
		}

		for (final IProgramVar rv : rankVarsWithDistinctOutVar) {
			final IReplacementVarOrConst varOrConst = getOrConstructReplacementVar(rv);
			if (varOrConst instanceof ReplacementConst) {
				throw new UnsupportedOperationException("not yet implemented");
			}
			final IReplacementVar repVar = (IReplacementVar) varOrConst;
			final TermVariable newOutVar = mVarFactory.getOrConstructAuxVar(
					computeTermVariableName(repVar.getGloballyUniqueId(), false, true), mRepVarSort);
			final Term replacementTerm = constructReplacementTerm(newOutVar);
			mSubstitutionMapping.put(tf.getOutVars().get(rv), replacementTerm);
			tf.removeOutVar(rv);
			tf.addOutVar(repVar, newOutVar);
		}

		final List<TermVariable> auxVars = new ArrayList<>(tf.getAuxVars());
		for (final TermVariable tv : auxVars) {
			if (hasToBeReplaced(tv)) {
				final TermVariable newAuxVar = mVarFactory
						.getOrConstructAuxVar(computeTermVariableName(tv.getName(), false, false), mRepVarSort);
				tf.removeAuxVar(tv);
				tf.addAuxVars(Collections.singleton(newAuxVar));
				final Term replacementTerm = constructReplacementTerm(newAuxVar);
				mSubstitutionMapping.put(tv, replacementTerm);
			}
		}
	}

	private final String computeTermVariableName(final String baseName, final boolean isInVar, final boolean isOutVar) {
		final String result;
		if (isInVar) {
			if (isOutVar) {
				result = baseName + "_inout_" + getTermVariableSuffix();
			} else {
				result = baseName + "_in_" + getTermVariableSuffix();
			}
		} else {
			if (isOutVar) {
				result = baseName + "_out_" + getTermVariableSuffix();
			} else {
				result = baseName + "_aux_" + getTermVariableSuffix();
			}
		}
		return result;
	}

	@Override
	public final ModifiableTransFormula process(final ManagedScript script, final ModifiableTransFormula tf)
			throws TermException {
		generateRepAndAuxVars(tf);
		final ModifiableTransFormula newTf = new ModifiableTransFormula(tf);
		final Term newFormula =
				new SubstitutionWithLocalSimplification(script, mSubstitutionMapping).transform(tf.getFormula());
		newTf.setFormula(newFormula);
		return newTf;
	}

}
