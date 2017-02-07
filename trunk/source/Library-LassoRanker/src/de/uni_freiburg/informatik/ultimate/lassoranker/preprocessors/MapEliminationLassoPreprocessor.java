/*
 * Copyright (C) 2016 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.Activator;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays.EqualitySupportingInvariantAnalysis;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoUnderConstruction;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.EqualityAnalysisResult;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination.MapEliminationSettings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination.MapEliminator;

/**
 * A Wrapper to apply {@link MapEliminator} to lasso-programs
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class MapEliminationLassoPreprocessor extends LassoPreprocessor {
	private static final String DESCRIPTION = "Removes maps (arrays and UFs) by introducing new variables for each relevant argument";

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mManagedScript;
	private final IIcfgSymbolTable mSymbolTable;
	private final ReplacementVarFactory mReplacementVarFactory;
	private final UnmodifiableTransFormula mOriginalStem;
	private final UnmodifiableTransFormula mOriginalLoop;
	private final Set<IProgramNonOldVar> mModifiableGlobalsAtHonda;
	private final Set<Term> mArrayIndexSupportingInvariants;
	private final MapEliminationSettings mSettings;

	public MapEliminationLassoPreprocessor(final IUltimateServiceProvider services, final ManagedScript managedScript,
			final IIcfgSymbolTable symbolTable, final ReplacementVarFactory replacementVarFactory,
			final UnmodifiableTransFormula originalStem, final UnmodifiableTransFormula originalLoop,
			final Set<IProgramNonOldVar> modifiableGlobalsAtHonda, final Set<Term> arrayIndexSupportingInvariants,
			final MapEliminationSettings settings) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		mManagedScript = managedScript;
		mSymbolTable = symbolTable;
		mReplacementVarFactory = replacementVarFactory;
		mOriginalStem = originalStem;
		mOriginalLoop = originalLoop;
		mModifiableGlobalsAtHonda = modifiableGlobalsAtHonda;
		mArrayIndexSupportingInvariants = arrayIndexSupportingInvariants;
		mSettings = settings;
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
		final MapEliminator elim = new MapEliminator(mServices, mLogger, mManagedScript, mSymbolTable,
				mReplacementVarFactory, Arrays.asList(lasso.getStem(), lasso.getLoop()), mSettings);
		final EqualityAnalysisResult equalityAnalysisStem = new EqualityAnalysisResult(elim.getDoubletons());
		final EqualitySupportingInvariantAnalysis esia = new EqualitySupportingInvariantAnalysis(elim.getDoubletons(),
				mSymbolTable, mManagedScript.getScript(), mOriginalStem, mOriginalLoop, mModifiableGlobalsAtHonda);
		final EqualityAnalysisResult equalityAnalysisLoop = esia.getEqualityAnalysisResult();
		mArrayIndexSupportingInvariants
				.addAll(equalityAnalysisLoop.constructListOfEqualities(mManagedScript.getScript()));
		mArrayIndexSupportingInvariants
				.addAll(equalityAnalysisLoop.constructListOfNotEquals(mManagedScript.getScript()));
		final ModifiableTransFormula newStem = elim.getRewrittenTransFormula(lasso.getStem(), equalityAnalysisStem,
				equalityAnalysisLoop);
		final ModifiableTransFormula newLoop = elim.getRewrittenTransFormula(lasso.getLoop(), equalityAnalysisLoop,
				equalityAnalysisLoop);
		final LassoUnderConstruction newLasso = new LassoUnderConstruction(newStem, newLoop);
		assert RewriteArrays2.checkStemImplication(mServices, mLogger, lasso, newLasso, mSymbolTable,
				mManagedScript) : "result of RewriteArrays too strong";
		return Collections.singleton(newLasso);
	}
}