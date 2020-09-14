/*
 * Copyright (C) 2020 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE accelerated interpolation library .
 *
 * The ULTIMATE framework is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE framework is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE accelerated interpolation library . If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PDR library , or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE accelerated interpolation library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.looppreprocessor;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.ModuloNeighborTransformation;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TermException;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.PredicateHelper;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;

/**
 * Preprocess a given loop by transforming not supported transitions.
 *
 * @author Jonas Werner <wernerj@informatik.uni-freiburg.de>
 *
 * @param <LETTER>
 *            transition type
 */
public class LoopPreprocessorFastUPR<LETTER extends IIcfgTransition<?>> implements ILoopPreprocessor<LETTER> {

	private final ManagedScript mScript;
	private final ILogger mLogger;
	private final IPredicateUnifier mPredUnifier;
	private final PredicateHelper<LETTER> mPredHelper;
	private final IUltimateServiceProvider mServices;
	private final ReplacementVarFactory mReplacementVarFactory;
	private final CfgSmtToolkit mCsToolkit;

	/**
	 * Remove for example modulo operations from a loop, because FastUPR does not support it.
	 *
	 * @param logger
	 * @param script
	 * @param predUnifier
	 */
	public LoopPreprocessorFastUPR(final ILogger logger, final ManagedScript script,
			final IUltimateServiceProvider services, final IPredicateUnifier predUnifier,
			final PredicateHelper<LETTER> predHelper, final CfgSmtToolkit toolkit) {
		mLogger = logger;
		mScript = script;
		mPredUnifier = predUnifier;
		mPredHelper = predHelper;
		mServices = services;
		mCsToolkit = toolkit;
		mReplacementVarFactory = new ReplacementVarFactory(mCsToolkit, false);
	}

	/**
	 * Preprocess a loop to remove unsupported operations, such as modulo
	 */
	@Override
	public Map<IcfgLocation, Set<List<LETTER>>> preProcessLoop(final Map<IcfgLocation, Set<List<LETTER>>> loop) {
		for (final Entry<IcfgLocation, Set<List<LETTER>>> loopSet : loop.entrySet()) {
			final IcfgLocation loophead = loopSet.getKey();

			for (final List<LETTER> loopTransitions : loopSet.getValue()) {
				final TransFormula loopRelation = mPredHelper.traceToTf(loopTransitions);
				final List<ApplicationTerm> modTermSubs = new ArrayList<>();
				final ModuloNeighborTransformation modNeighborTransformer =
						new ModuloNeighborTransformation(mServices, true);
				final ModifiableTransFormula modTf =
						ModifiableTransFormulaUtils.buildTransFormula(loopRelation, mReplacementVarFactory, mScript);
				ModifiableTransFormula modTfTransformed;
				try {
					modTfTransformed = modNeighborTransformer.process(mScript, modTf);
				} catch (final TermException e) {
					modTfTransformed = null;
					e.printStackTrace();
				}
				if (modTfTransformed != null) {
					final ApplicationTermFinder applicationTermFinder = new ApplicationTermFinder("mod", true);
					final Set<ApplicationTerm> remainModTerms =
							applicationTermFinder.findMatchingSubterms(modTfTransformed.getFormula());
					mLogger.debug("remaining mods");
				}
			}
			mLogger.debug("Found modulo");
		}

		return loop;
	}

}