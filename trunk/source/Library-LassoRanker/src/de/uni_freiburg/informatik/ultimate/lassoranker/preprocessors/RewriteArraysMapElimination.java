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
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplicationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.EqualityAnalysisResult;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * Replace term with arrays by term without arrays by introducing replacement variables for all "important" array values
 * and equalities that state the constraints between array indices and array values (resp. their replacement variables).
 *
 * @author Frank Schüssele
 */
public class RewriteArraysMapElimination extends LassoPreprocessor {
	private static final String DESCRIPTION = "Removes arrays by introducing new variables for each relevant array cell";

	// Parameters for the MapEliminator
	private static boolean ADD_INEQUALITIES = false;
	private static boolean ADD_INDEX_ASSIGNMENT = false;
	private static boolean ONLY_TRIVIAL_IMPLICATIONS = false;
	private static boolean ONLY_INDICES_IN_FORMULA = true;

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final Boogie2SmtSymbolTable mSymbolTable;
	private final ReplacementVarFactory mReplacementVarFactory;
	private final UnmodifiableTransFormula mOriginalStem;
	private final UnmodifiableTransFormula mOriginalLoop;
	private final Set<IProgramVar> mModifiableGlobalsAtHonda;
	private final SimplicationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final Set<Term> mArrayIndexSupportingInvariants;

	public RewriteArraysMapElimination(final IUltimateServiceProvider services, final ManagedScript managedScript,
			final Boogie2SmtSymbolTable symbolTable, final ReplacementVarFactory replacementVarFactory,
			final UnmodifiableTransFormula originalStem, final UnmodifiableTransFormula originalLoop,
			final Set<IProgramVar> modifiableGlobalsAtHonda, final SimplicationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final Set<Term> arrayIndexSupportingInvariants) {
		mServices = services;
		mManagedScript = managedScript;
		mSymbolTable = symbolTable;
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
		return DESCRIPTION;
	}

	@Override
	public Collection<LassoUnderConstruction> process(final LassoUnderConstruction lasso) throws TermException {
		final MapEliminator elim = new MapEliminator(mServices, mManagedScript, mSymbolTable, mReplacementVarFactory,
				mSimplificationTechnique, mXnfConversionTechnique, Arrays.asList(lasso.getStem(), lasso.getLoop()),
				ADD_INEQUALITIES, ADD_INDEX_ASSIGNMENT, ONLY_TRIVIAL_IMPLICATIONS, ONLY_INDICES_IN_FORMULA);
		final EqualityAnalysisResult equalityAnalysisStem = new EqualityAnalysisResult(elim.getDoubletons());
		final EqualitySupportingInvariantAnalysis esia = new EqualitySupportingInvariantAnalysis(elim.getDoubletons(),
				mSymbolTable, mManagedScript.getScript(), mOriginalStem, mOriginalLoop, mModifiableGlobalsAtHonda);
		final EqualityAnalysisResult equalityAnalysisLoop = esia.getEqualityAnalysisResult();
		mArrayIndexSupportingInvariants
				.addAll(equalityAnalysisLoop.constructListOfEqualities(mManagedScript.getScript()));
		mArrayIndexSupportingInvariants
				.addAll(equalityAnalysisLoop.constructListOfNotEquals(mManagedScript.getScript()));
		final TransFormulaLR newStem = elim.getRewrittenTransFormula(lasso.getStem(), equalityAnalysisStem,
				equalityAnalysisLoop);
		final TransFormulaLR newLoop = elim.getRewrittenTransFormula(lasso.getLoop(), equalityAnalysisLoop,
				equalityAnalysisLoop);
		final LassoUnderConstruction newLasso = new LassoUnderConstruction(newStem, newLoop);
		return Collections.singleton(newLasso);
	}
}
