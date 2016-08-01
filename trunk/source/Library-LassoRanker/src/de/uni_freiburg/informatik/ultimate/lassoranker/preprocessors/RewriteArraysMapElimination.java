/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.mapelimination.MapEliminator;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays.EqualitySupportingInvariantAnalysis;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoUnderConstruction;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.VariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplicationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.EqualityAnalysisResult;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.variables.IProgramVar;

/**
 * Replace term with arrays by term without arrays by introducing replacement variables for all "important" array values
 * and equalities that state the constraints between array indices and array values (resp. their replacement variables).
 *
 * @author Frank Schüssele
 */
public class RewriteArraysMapElimination extends LassoPreprocessor {
	public static final String s_Description = "Removes arrays by introducing new variables for each relevant array cell";

	private final IUltimateServiceProvider mServices;
	private final Script mScript;
	private final Boogie2SmtSymbolTable mSymbolTable;
	private final VariableManager mVariableManager;
	private final ReplacementVarFactory mReplacementVarFactory;
	private final TransFormula mOriginalStem;
	private final TransFormula mOriginalLoop;
	private final Set<IProgramVar> mModifiableGlobalsAtHonda;
	private final SimplicationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final Set<Term> mArrayIndexSupportingInvariants;

	public RewriteArraysMapElimination(final IUltimateServiceProvider services, final Script script,
			final Boogie2SmtSymbolTable symbolTable, final VariableManager variableManager,
			final ReplacementVarFactory replacementVarFactory, final TransFormula originalStem,
			final TransFormula originalLoop, final Set<IProgramVar> modifiableGlobalsAtHonda,
			final SimplicationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final Set<Term> arrayIndexSupportingInvariants) {
		mServices = services;
		mScript = script;
		mSymbolTable = symbolTable;
		mVariableManager = variableManager;
		mReplacementVarFactory = replacementVarFactory;
		mOriginalStem = originalStem;
		mOriginalLoop = originalLoop;
		mModifiableGlobalsAtHonda = modifiableGlobalsAtHonda;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mArrayIndexSupportingInvariants = arrayIndexSupportingInvariants;

	}

	@Override
	public String getName() {
		return getClass().getSimpleName();
	}

	@Override
	public String getDescription() {
		return s_Description;
	}

	@Override
	public Collection<LassoUnderConstruction> process(final LassoUnderConstruction lasso) throws TermException {
		final MapEliminator elim = new MapEliminator(mServices, mScript, mSymbolTable, mVariableManager,
				mReplacementVarFactory, mSimplificationTechnique, mXnfConversionTechnique,
				Arrays.asList(lasso.getStem(), lasso.getLoop()));
		final EqualityAnalysisResult equalityAnalysisStem = new EqualityAnalysisResult(elim.getDoubletons());
		final EqualitySupportingInvariantAnalysis esia = new EqualitySupportingInvariantAnalysis(elim.getDoubletons(),
				mSymbolTable, mScript, mOriginalStem, mOriginalLoop, mModifiableGlobalsAtHonda);
		final EqualityAnalysisResult equalityAnalysisLoop = esia.getEqualityAnalysisResult();
		mArrayIndexSupportingInvariants.addAll(equalityAnalysisLoop.constructListOfEqualities(mScript));
		mArrayIndexSupportingInvariants.addAll(equalityAnalysisLoop.constructListOfNotEquals(mScript));
		final TransFormulaLR newStem = elim.getArrayFreeTransFormula(lasso.getStem(), equalityAnalysisStem,
				equalityAnalysisLoop);
		final TransFormulaLR newLoop = elim.getArrayFreeTransFormula(lasso.getLoop(), equalityAnalysisLoop,
				equalityAnalysisLoop);
		final LassoUnderConstruction newLasso = new LassoUnderConstruction(newStem, newLoop);
		return Collections.singleton(newLasso);
	}
}
