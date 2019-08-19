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

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.Activator;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays.ArrayCellRepVarConstructor;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays.ArrayCellReplacementVarInformation;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays.EqualitySupportingInvariantAnalysis;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays.TransFormulaLRWithArrayCells;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays.TransFormulaLRWithArrayInformation;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoUnderConstruction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.equalityanalysis.EqualityAnalysisResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Replace term with arrays by term without arrays by introducing replacement variables for all "important" array values
 * and equalities that state the constraints between array indices and array values (resp. their replacement variables).
 *
 *
 * @author Matthias Heizmann
 */
public class RewriteArrays2 extends LassoPreprocessor {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

	public static final boolean ADDITIONAL_CHECKS_IF_ASSERTIONS_ENABLED = !false;

	public static final String DESCRIPTION = "Removes arrays by introducing new variables for each relevant array cell";

	static final String AUX_ARRAY = "auxArray";

	/**
	 * The script used to transform the formula
	 */
	private final ManagedScript mScript;

	// private final boolean mSearchAdditionalSupportingInvariants;
	private final UnmodifiableTransFormula mOriginalStem;
	private final UnmodifiableTransFormula mOriginalLoop;
	private final Set<Term> mArrayIndexSupportingInvariants;
	private final Set<IProgramNonOldVar> mModifiableGlobalsAtHonda;

	private final ReplacementVarFactory mReplacementVarFactory;
	private final ManagedScript mFreshTermVariableConstructor;
	private final IIcfgSymbolTable mBoogie2Smt;

	private final boolean mOverapproximateByOmmitingDisjointIndices;

	public RewriteArrays2(final boolean overapproximateByOmmitingDisjointIndices, final UnmodifiableTransFormula originalStem,
			final UnmodifiableTransFormula originalLoop, final Set<IProgramNonOldVar> modifiableGlobalsAtHonda,
			final IUltimateServiceProvider services, final Set<Term> arrayIndexSupportingInvariants,
			final IIcfgSymbolTable boogie2smt, final ManagedScript mgdScript, final ReplacementVarFactory ReplacementVarFactory,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mOriginalStem = originalStem;
		mOriginalLoop = originalLoop;
		mModifiableGlobalsAtHonda = modifiableGlobalsAtHonda;
		mArrayIndexSupportingInvariants = arrayIndexSupportingInvariants;
		mOverapproximateByOmmitingDisjointIndices = overapproximateByOmmitingDisjointIndices;
		mBoogie2Smt = boogie2smt;
		mScript = mgdScript;
		mReplacementVarFactory = ReplacementVarFactory;
		mFreshTermVariableConstructor = mScript;
	}

	@Override
	public String getName() {
		return getClass().getSimpleName();
	}

	@Override
	public String getDescription() {
		return DESCRIPTION;
	}

	// @Override
	// public void process(LassoBuilder lasso_builder)
	// throws TermException {
	// mlassoBuilder = lasso_builder;
	// mScript = lasso_builder.getScript();
	// ReplacementVarFactory replacementVarFactory = lasso_builder.getReplacementVarFactory();
	//
	// Collection<TransFormulaLR> old_stemcomponents = lasso_builder.getStemComponentsTermination();
	//// assert old_stemcomponents == lasso_builder.getStemComponentsNonTermination();
	// Collection<TransFormulaLR> old_loop_components = lasso_builder.getLoopComponentsTermination();
	//// assert old_loop_components == lasso_builder.getLoopComponentsNonTermination();
	// List<TransFormulaLRWithArrayInformation> stemComponents1 = new ArrayList<TransFormulaLRWithArrayInformation>();
	// for (TransFormulaLR stemComponent : old_stemcomponents) {
	// TransFormulaLRWithArrayInformation test = new TransFormulaLRWithArrayInformation(
	// mServices, stemComponent, replacementVarFactory, mScript, mlassoBuilder.getBoogie2SMT().getVariableManager(),
	// null);
	// stemComponents1.add(test);
	// }
	// List<TransFormulaLRWithArrayInformation> loopComponents1 = new ArrayList<TransFormulaLRWithArrayInformation>();
	// for (TransFormulaLR loopComponent : old_loop_components) {
	// TransFormulaLRWithArrayInformation test = new TransFormulaLRWithArrayInformation(
	// mServices, loopComponent, replacementVarFactory, mScript, mlassoBuilder.getBoogie2SMT().getVariableManager(),
	// stemComponents1);
	// loopComponents1.add(test);
	// }
	// ArrayCellRepVarConstructor acrvc = new ArrayCellRepVarConstructor(replacementVarFactory, mScript,
	// stemComponents1, loopComponents1);
	// IndexSupportingInvariantAnalysis isia = new IndexSupportingInvariantAnalysis(acrvc, true,
	// lasso_builder.getBoogie2SMT(), mOriginalStem, mOriginalLoop, mModifiableGlobalsAtHonda);
	// mArrayIndexSupportingInvariants.addAll(isia.getAdditionalConjunctsEqualities());
	// mArrayIndexSupportingInvariants.addAll(isia.getAdditionalConjunctsNotEquals());
	//
	// // for termination, we overapproximate by ommiting disjoint indices
	// {
	// List<TransFormulaLRWithArrayCells> stemComponents2 = new ArrayList<TransFormulaLRWithArrayCells>();
	// List<TransFormulaLR> new_stemcomponents = new ArrayList<TransFormulaLR>(old_stemcomponents.size());
	// for (TransFormulaLRWithArrayInformation stemComponent : stemComponents1) {
	// TransFormulaLRWithArrayCells test = new TransFormulaLRWithArrayCells(mServices, replacementVarFactory, mScript,
	// stemComponent, isia, lasso_builder.getBoogie2SMT(), null, true, true);
	// stemComponents2.add(test);
	// new_stemcomponents.add(test.getResult());
	// }
	// lasso_builder.setStemComponentsTermination(new_stemcomponents);
	// }
	//
	// // for nontermination, we do not overapproximate
	// {
	// List<TransFormulaLRWithArrayCells> stemComponents2 = new ArrayList<TransFormulaLRWithArrayCells>();
	// List<TransFormulaLR> new_stemcomponents = new ArrayList<TransFormulaLR>(old_stemcomponents.size());
	// for (TransFormulaLRWithArrayInformation stemComponent : stemComponents1) {
	// TransFormulaLRWithArrayCells test = new TransFormulaLRWithArrayCells(mServices, replacementVarFactory, mScript,
	// stemComponent, isia, lasso_builder.getBoogie2SMT(), null, false, true);
	// stemComponents2.add(test);
	// new_stemcomponents.add(test.getResult());
	// }
	// lasso_builder.setStemComponentsNonTermination(new_stemcomponents);
	// }
	//
	// // for termination, we overapproximate by ommiting disjoint indices
	// {
	// List<TransFormulaLRWithArrayCells> loopComponents2 = new ArrayList<TransFormulaLRWithArrayCells>();
	// List<TransFormulaLR> new_loop_components = new ArrayList<TransFormulaLR>(old_loop_components.size());
	// for (TransFormulaLRWithArrayInformation loopComponent : loopComponents1) {
	// TransFormulaLRWithArrayCells test = new TransFormulaLRWithArrayCells(mServices, replacementVarFactory, mScript,
	// loopComponent, isia, lasso_builder.getBoogie2SMT(), acrvc, true, false);
	// loopComponents2.add(test);
	// new_loop_components.add(test.getResult());
	// }
	//
	// lasso_builder.setLoopComponentsTermination(new_loop_components);
	// }
	//
	// // for nontermination, we do not overapproximate
	// {
	// List<TransFormulaLRWithArrayCells> loopComponents2 = new ArrayList<TransFormulaLRWithArrayCells>();
	// List<TransFormulaLR> new_loop_components = new ArrayList<TransFormulaLR>(old_loop_components.size());
	// for (TransFormulaLRWithArrayInformation loopComponent : loopComponents1) {
	// TransFormulaLRWithArrayCells test = new TransFormulaLRWithArrayCells(mServices, replacementVarFactory, mScript,
	// loopComponent, isia, lasso_builder.getBoogie2SMT(), acrvc, false, false);
	// loopComponents2.add(test);
	// new_loop_components.add(test.getResult());
	// }
	//
	// lasso_builder.setLoopComponentsNonTermination(new_loop_components);
	// }
	//
	//
	// }

	@Override
	public Collection<LassoUnderConstruction> process(final LassoUnderConstruction lasso) throws TermException {
		final boolean overapproximate = true;
		final TransFormulaLRWithArrayInformation stemTfwai =
				new TransFormulaLRWithArrayInformation(mServices, lasso.getStem(), mReplacementVarFactory, mScript,
						mBoogie2Smt, null, mSimplificationTechnique, mXnfConversionTechnique);
		final TransFormulaLRWithArrayInformation loopTfwai =
				new TransFormulaLRWithArrayInformation(mServices, lasso.getLoop(), mReplacementVarFactory, mScript,
						mBoogie2Smt, stemTfwai, mSimplificationTechnique, mXnfConversionTechnique);
		final ArrayCellRepVarConstructor acrvc =
				new ArrayCellRepVarConstructor(mReplacementVarFactory, mScript.getScript(), stemTfwai, loopTfwai);
		final EqualityAnalysisResult equalityAnalysisAtHonda;
		{
			final EqualitySupportingInvariantAnalysis isia = new EqualitySupportingInvariantAnalysis(
					computeDoubletons(acrvc), mBoogie2Smt, mScript.getScript(), mOriginalStem,
					mOriginalLoop, mModifiableGlobalsAtHonda);
			equalityAnalysisAtHonda = isia.getEqualityAnalysisResult();
		}
		mArrayIndexSupportingInvariants.addAll(equalityAnalysisAtHonda.constructListOfEqualities(mScript.getScript()));
		mArrayIndexSupportingInvariants.addAll(equalityAnalysisAtHonda.constructListOfNotEquals(mScript.getScript()));
		final TransFormulaLRWithArrayCells stem = new TransFormulaLRWithArrayCells(mServices, mReplacementVarFactory,
				mScript, stemTfwai, equalityAnalysisAtHonda, mBoogie2Smt, null, overapproximate, true,
				mSimplificationTechnique, mXnfConversionTechnique);
		final TransFormulaLRWithArrayCells loop = new TransFormulaLRWithArrayCells(mServices, mReplacementVarFactory,
				mScript, loopTfwai, equalityAnalysisAtHonda, mBoogie2Smt, acrvc, overapproximate, false,
				mSimplificationTechnique, mXnfConversionTechnique);
		final LassoUnderConstruction newLasso = new LassoUnderConstruction(stem.getResult(), loop.getResult());
		assert !ADDITIONAL_CHECKS_IF_ASSERTIONS_ENABLED || checkStemImplication(mServices, mLogger, lasso, newLasso,
				mBoogie2Smt, mScript) : "result of RewriteArrays too strong";
		return Collections.singleton(newLasso);
	}

	private Set<Doubleton<Term>> computeDoubletons(final ArrayCellRepVarConstructor arrayCellRepVarConstructor) {
		final NestedMap2<TermVariable, ArrayIndex, ArrayCellReplacementVarInformation> array2index2repVar =
				arrayCellRepVarConstructor.getArrayRepresentative2IndexRepresentative2ReplacementVar();
		final Set<Doubleton<Term>> result = new LinkedHashSet<>();
		for (final TermVariable array : array2index2repVar.keySet()) {
			final Set<ArrayIndex> allIndices = array2index2repVar.get(array).keySet();
			final ArrayIndex[] allIndicesArr = allIndices.toArray(new ArrayIndex[allIndices.size()]);
			for (int i = 0; i < allIndicesArr.length; i++) {
				for (int j = i + 1; j < allIndicesArr.length; j++) {
					final List<Term> fstIndex = allIndicesArr[i];
					final List<Term> sndIndex = allIndicesArr[j];
					assert fstIndex.size() == sndIndex.size();
					for (int k = 0; k < fstIndex.size(); k++) {
						final Doubleton<Term> doubleton = new Doubleton<Term>(fstIndex.get(k), sndIndex.get(k));
						result.add(doubleton);
					}
				}
			}
		}
		return result;
	}

	public static boolean checkStemImplication(final IUltimateServiceProvider services, final ILogger logger,
			final LassoUnderConstruction oldLasso, final LassoUnderConstruction newLasso, 
			final IIcfgSymbolTable boogie2smt, final ManagedScript script) {
		final LBool implies = ModifiableTransFormulaUtils.implies(services, logger, oldLasso.getStem(), newLasso.getStem(),
				script.getScript(), boogie2smt);
		if (implies != LBool.SAT && implies != LBool.UNSAT) {
			logger.warn("result of RewriteArrays check is " + implies);
		}
		assert (implies != LBool.SAT) : "result of RewriteArrays too strong";
		return (implies != LBool.SAT);
	}

}
