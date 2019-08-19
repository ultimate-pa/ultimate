/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lassoranker.variables;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.Lasso;
import de.uni_freiburg.informatik.ultimate.lassoranker.LassoAnalysis.PreprocessingBenchmark;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearTransition;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.LassoPreprocessor;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.InequalityConverter.NlaHandling;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * The LassoBuilder class holds the lasso components during preprocessing.
 *
 * This object is *not* immutable.
 *
 * @author Jan Leike
 * @author Matthias Heizmann
 */
public class LassoBuilder {
	/**
	 * The Boogie2SMT object
	 */
	private final ManagedScript mMgdScript;

	/**
	 * Collection of all generated replacement TermVariables
	 */
	private final Collection<TermVariable> mtermVariables;

	/**
	 * Conjunctive representation of the lassos during the preprocessing.
	 */
	private List<LassoUnderConstruction> mLassosUC;

	private Collection<Lasso> mLassos;

	/**
	 * Object that has to be used for getting and constructing ReplacementVars that occur in this LassoBuilder.
	 */
	private final ReplacementVarFactory mReplacementVarFactory;

	private PreprocessingBenchmark mPreprocessingBenchmark;

	private final ILogger mLogger;

	private final NlaHandling mNlaHandling;

	/**
	 * Create a new LassoBuilder object from components
	 *
	 * @param script
	 *            the script that created the transition formulae
	 * @param stem
	 *            the stem transition
	 * @param loop
	 *            the loop transition
	 */
	public LassoBuilder(final ILogger logger, final CfgSmtToolkit csToolkit,
			final UnmodifiableTransFormula stem, final UnmodifiableTransFormula loop, final NlaHandling nlaHandling) {
		mLogger = logger;
		mMgdScript = csToolkit.getManagedScript();
		mNlaHandling = nlaHandling;
		mtermVariables = new ArrayList<>();

		mReplacementVarFactory = new ReplacementVarFactory(csToolkit, true);

		mLassosUC = new ArrayList<>();
		mLassosUC.add(
				new LassoUnderConstruction(ModifiableTransFormulaUtils.buildTransFormula(stem, mReplacementVarFactory, mMgdScript),
						ModifiableTransFormulaUtils.buildTransFormula(loop, mReplacementVarFactory, mMgdScript)));
	}

	public ReplacementVarFactory getReplacementVarFactory() {
		return mReplacementVarFactory;
	}

	/**
	 * @return a collection of all new TermVariable's created with this object
	 */
	public Collection<TermVariable> getGeneratedTermVariables() {
		return Collections.unmodifiableCollection(mtermVariables);
	}

	// /**
	// * Is the stem the same for termination analysis and nontermination analysis?
	// * @return whether getStemComponentsTermination() == getStemComponentsNonTermination()
	// */
	// public boolean isStemApproximated() {
	// return mstem_components_t != mstem_components_nt;
	// }
	//
	// /**
	// * Is the loop the same for termination analysis and nontermination analysis?
	// * @return whether getLoopComponentsTermination() == getLoopComponentsNonTermination()
	// */
	// public boolean isLoopApproximated() {
	// return mloop_components_t != mloop_components_nt;
	// }

	/**
	 * @return the conjunction of lassos
	 */
	public List<LassoUnderConstruction> getLassosUC() {
		return mLassosUC;
	}

	public void applyPreprocessor(final LassoPreprocessor preprocessor) throws TermException {
		final ArrayList<LassoUnderConstruction> newLassos = new ArrayList<>();
		for (final LassoUnderConstruction lasso : mLassosUC) {
			try {
				newLassos.addAll(preprocessor.process(lasso));
			} catch (final ToolchainCanceledException tce) {
				final String taskDescription = "applying " + preprocessor.getName() + " to lasso for termination ";
				tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
				throw tce;
			}
		}
		mLassosUC = newLassos;
	}

	/**
	 * Run a few sanity checks
	 *
	 * @param task
	 *            task that run before construction of this lasso
	 * @return false if something is fishy
	 */
	public boolean isSane(final String task) {
		boolean sane = true;
		for (final LassoUnderConstruction luc : mLassosUC) {
			sane &= luc.getStem().auxVarsDisjointFromInOutVars();
			assert sane : "inconsistent lasso after " + task + ": auxVarsDisjointFromInOutVars";
			sane &= luc.getStem().allAreInOutAux(luc.getStem().getFormula().getFreeVars()) == null;
			assert sane : "inconsistent lasso after " + task + ": allAreInOutAux";
			sane &= luc.getLoop().auxVarsDisjointFromInOutVars();
			assert sane : "inconsistent lasso after " + task + ": auxVarsDisjointFromInOutVars";
			sane &= luc.getLoop().allAreInOutAux(luc.getLoop().getFormula().getFreeVars()) == null;
			assert sane : "inconsistent lasso after " + task + ": allAreInOutAux";
		}
		return sane;
	}

	/**
	 * Construct a polyhedron representation for each component of stem and loop.
	 *
	 * Only succeeds if the transition formulas are of the required form, i.e., if preprocessing has been completed.
	 *
	 * @throws TermException
	 *             if the transition formulas are not of the correct form
	 */
	public void constructPolyhedra() throws TermException {
		final int n = mLassosUC.size();
		final List<Lasso> lassos = new ArrayList<>(n);
		for (int i = 0; i < n; ++i) {
			final ModifiableTransFormula stemTF = mLassosUC.get(i).getStem();
			final ModifiableTransFormula loopTF = mLassosUC.get(i).getLoop();
			final LinearTransition stem = LinearTransition.fromTransFormulaLR(stemTF, mNlaHandling);
			final LinearTransition loop = LinearTransition.fromTransFormulaLR(loopTF, mNlaHandling);
			lassos.add(new Lasso(stem, loop));
		}
		mLassos = lassos;
	}

	/**
	 * @return a colletion of lassos, one for each component
	 * @throws TermException
	 *             if the transition formulas are not of the correct form
	 */
	public Collection<Lasso> getLassos() {
		return mLassos;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		if (mLassos == null) {
			sb.append("Preprocessing has not been completed.\n");

			sb.append("Current lassos:\n");
			for (final LassoUnderConstruction luc : mLassosUC) {
				sb.append(luc);
				sb.append(System.lineSeparator());
			}
		} else {
			sb.append("Lassos:\n");
			for (final Lasso lasso : mLassos) {
				sb.append(lasso);
				sb.append("\n");
			}
		}
		return sb.toString();
	}

	public static long computeMaxDagSize(final List<LassoUnderConstruction> lassos) {
		if (lassos.isEmpty()) {
			return 0;
		}
		final long[] sizes = new long[lassos.size()];
		for (int i = 0; i < lassos.size(); ++i) {
			sizes[i] = lassos.get(i).getFormulaSize();
		}
		Arrays.sort(sizes);
		return sizes[lassos.size() - 1];
	}

	public long computeMaxDagSize() {
		return computeMaxDagSize(mLassosUC);
	}

	public void preprocess(final LassoPreprocessor[] preProcessorsTermination,
			final LassoPreprocessor[] preProcessorsNontermination) throws TermException {
		mPreprocessingBenchmark = new PreprocessingBenchmark(computeMaxDagSize());
		// Apply preprocessors
		for (final LassoPreprocessor preprocessor : preProcessorsTermination) {
			if (preprocessor == null) {
				continue;
			}
			mLogger.debug(preprocessor.getDescription());
			applyPreprocessor(preprocessor);
			mPreprocessingBenchmark.addPreprocessingData(preprocessor.getDescription(), computeMaxDagSize());
			assert isSane(preprocessor.getClass().getSimpleName()) : "lasso failed sanity check";
		}

	}

	public PreprocessingBenchmark getPreprocessingBenchmark() {
		return mPreprocessingBenchmark;
	}

}
