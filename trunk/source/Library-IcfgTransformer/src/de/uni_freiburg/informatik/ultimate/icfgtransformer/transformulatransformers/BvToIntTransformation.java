/*
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

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.IReplacementVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.bvinttranslation.TranslationConstrainer.ConstraintsForBitwiseOperations;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.bvinttranslation.TranslationManager;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public class BvToIntTransformation extends TransitionPreprocessor {
	public static final String DESCRIPTION = "Translate Bitvectors to Integer Formulas";

	private final IUltimateServiceProvider mServices;
	private final ReplacementVarFactory mFac;

	final LinkedHashMap<Term, Term> mBacktranslationMap = new LinkedHashMap<>();

	private final boolean mUseCongruenceBasedTransformation;

	/**
	 * @param fac
	 * @param mgdScript
	 * @param useNeighbors
	 *            If set to false we obtain the underapproximation where we assume that the modulo operator is the
	 *            identity for the first argument.
	 */
	public BvToIntTransformation(final IUltimateServiceProvider services, final ReplacementVarFactory fac,
			final ManagedScript mgdScript, final boolean useCongruenceBasedTransformation) {
		super();
		mFac = fac;
		mServices = services;
		mUseCongruenceBasedTransformation = useCongruenceBasedTransformation;
	}

	@Override
	public String getDescription() {
		return DESCRIPTION;
	}

	@Override
	public ModifiableTransFormula process(final ManagedScript mgdScript, final ModifiableTransFormula tf)
			throws TermException {

		if (!tf.getNonTheoryConsts().isEmpty()) {
			throw new UnsupportedOperationException("Non-theory constants: " + tf.getNonTheoryConsts());
		}

		// final TransFormulaBuilder newIntTF = new TransFormulaBuilder(null,
		// null, false, null, false, null, false);
		final ModifiableTransFormula newIntTF = new ModifiableTransFormula(tf);

		final LinkedHashMap<Term, Term> varMap = new LinkedHashMap<>();
		for (final IProgramVar progVar : TransFormula.collectAllProgramVars(tf)) {

			final IReplacementVarOrConst repVar = mFac.getOrConstuctReplacementVar(progVar.getTermVariable(), true,
					bvToIntSort(mgdScript, progVar.getTerm().getSort()));
			mBacktranslationMap.put(((IProgramVar) repVar).getTermVariable(), progVar.getTermVariable());

			final TermVariable intInVar;
			final TermVariable intOutVar;

			if ((tf.getInVars().get(progVar) != null) && (tf.getOutVars().get(progVar) != null)) {
				if (tf.getInVars().get(progVar).equals(tf.getOutVars().get(progVar))) {
					final TermVariable intInAndOutVar = mgdScript.constructFreshTermVariable("intInAndOutVar",
							bvToIntSort(mgdScript, tf.getInVars().get(progVar).getSort()));
					intInVar = intInAndOutVar;
					intOutVar = intInAndOutVar;
				} else {

					intInVar = mgdScript.constructFreshTermVariable("intInVar",
							bvToIntSort(mgdScript, tf.getInVars().get(progVar).getSort()));

					intOutVar = mgdScript.constructFreshTermVariable("intOutVar",
							bvToIntSort(mgdScript, tf.getOutVars().get(progVar).getSort()));
				}
				varMap.put(tf.getInVars().get(progVar), intInVar);
				newIntTF.addInVar((IProgramVar) repVar, intInVar);
				varMap.put(tf.getOutVars().get(progVar), intOutVar);
				newIntTF.addOutVar((IProgramVar) repVar, intOutVar);
			} else {
				if (tf.getInVars().get(progVar) != null) {
					intInVar = mgdScript.constructFreshTermVariable("intInVar",
							bvToIntSort(mgdScript, tf.getInVars().get(progVar).getSort()));
					newIntTF.addInVar((IProgramVar) repVar, intInVar);
					varMap.put(tf.getInVars().get(progVar), intInVar);
				}
				if (tf.getOutVars().get(progVar) != null) {
					intOutVar = mgdScript.constructFreshTermVariable("intOutVar",
							bvToIntSort(mgdScript, tf.getOutVars().get(progVar).getSort()));
					newIntTF.addOutVar((IProgramVar) repVar, intOutVar);
					varMap.put(tf.getOutVars().get(progVar), intOutVar);
				}
			}
		}

		// construct new auxVar for each existing auxVar
		for (final TermVariable auxVar : tf.getAuxVars()) {
			final TermVariable newAuxVar =
					mgdScript.constructFreshTermVariable(auxVar.getName(), bvToIntSort(mgdScript, auxVar.getSort()));
			varMap.put(auxVar, newAuxVar);
			newIntTF.addAuxVars(Collections.singleton(newAuxVar));
		}

		final TranslationManager translationManager =
				new TranslationManager(mgdScript, ConstraintsForBitwiseOperations.SUM, mUseCongruenceBasedTransformation);
		translationManager.setReplacementVarMaps(varMap);

		final Triple<Term, Set<TermVariable>, Boolean> translated =
				translationManager.translateBvtoInt(tf.getFormula());
		if (!translated.getSecond().isEmpty() || translated.getThird()) {
			throw new UnsupportedOperationException();
		}

		newIntTF.setFormula(translated.getFirst());
		return newIntTF;
	}

	public static Sort bvToIntSort(final ManagedScript mgdScript, final Sort sort) {
		if (SmtSortUtils.isBitvecSort(sort)) {
			return SmtSortUtils.getIntSort(mgdScript);
		} else if (SmtSortUtils.isArraySort(sort)) {
			final Sort[] newArgs = new Sort[sort.getArguments().length];
			for (int i = 0; i < sort.getArguments().length; i++) {
				newArgs[i] = bvToIntSort(mgdScript, sort.getArguments()[i]);
			}
			assert newArgs.length == 2;
			final Sort domainSort = newArgs[0];
			final Sort rangeSort = newArgs[1];
			return SmtSortUtils.getArraySort(mgdScript.getScript(), domainSort, rangeSort);
		} else if (SmtSortUtils.isBoolSort(sort)) {
			return sort;
		} else {
			return sort;
			// throw new UnsupportedOperationException("Unexpected Sort: " + sort);
		}

	}

	@Override
	public boolean checkSoundness(final Script script, final ModifiableTransFormula oldTF,
			final ModifiableTransFormula newTF) {
		return true; // TODO
	}

	public LinkedHashMap<Term, Term> getBacktranslationOfVariables() {
		return mBacktranslationMap;
	}

}
