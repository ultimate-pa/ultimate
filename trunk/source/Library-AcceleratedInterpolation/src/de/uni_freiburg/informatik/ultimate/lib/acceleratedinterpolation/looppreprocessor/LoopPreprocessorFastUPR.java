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
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.DNF;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.ModuloNeighborTransformation;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RemoveNegation;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteDisequality;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteDivision;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TermException;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.PredicateHelper;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Preprocess a given loop by transforming not supported transitions.
 *
 * @author Jonas Werner <wernerj@informatik.uni-freiburg.de>
 *
 * @param <LETTER>
 *            transition type
 */
public class LoopPreprocessorFastUPR<LETTER extends IIcfgTransition<?>>
		implements ILoopPreprocessor<IcfgLocation, UnmodifiableTransFormula> {

	private final ManagedScript mScript;
	private final ILogger mLogger;
	// private final IPredicateUnifier mPredUnifier;
	private final PredicateHelper<LETTER> mPredHelper;
	private final IUltimateServiceProvider mServices;
	private final ReplacementVarFactory mReplacementVarFactory;
	private final CfgSmtToolkit mCsToolkit;
	private final List<String> mOptions;

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
		// mPredUnifier = predUnifier;
		mPredHelper = predHelper;
		mServices = services;
		mCsToolkit = toolkit;
		mReplacementVarFactory = new ReplacementVarFactory(mCsToolkit, false);

		mOptions = new ArrayList<>(Arrays.asList("mod", "not"));
	}

	/**
	 * Preprocess a loop to remove unsupported operations, such as modulo
	 */
	@Override
	public Map<IcfgLocation, List<UnmodifiableTransFormula>>
			preProcessLoop(final Map<IcfgLocation, Set<List<UnmodifiableTransFormula>>> loop) {
		final Map<IcfgLocation, List<UnmodifiableTransFormula>> result = new HashMap<>();

		for (final Entry<IcfgLocation, Set<List<UnmodifiableTransFormula>>> loopSet : loop.entrySet()) {
			final IcfgLocation loophead = loopSet.getKey();
			if (loopSet.getValue() == null) {
				continue;
			}
			final List<UnmodifiableTransFormula> disjuncts = new ArrayList<>();
			for (final List<UnmodifiableTransFormula> loopTransitions : loopSet.getValue()) {
				UnmodifiableTransFormula loopRelation = TransFormulaUtils.sequentialComposition(mLogger, mServices,
						mScript, true, true, false, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION,
						SimplificationTechnique.SIMPLIFY_DDA, loopTransitions);
				/*
				 * Transform found unsupported operations:
				 */
				for (final String option : mOptions) {
					final ApplicationTermFinder applicationTermFinder = new ApplicationTermFinder(option, false);
					if (!applicationTermFinder.findMatchingSubterms(loopRelation.getFormula()).isEmpty()) {
						loopRelation = preProcessing(option, loopRelation);
					}
					mLogger.debug("Preprocess");
				}
				disjuncts.addAll(splitDisjunction(loopRelation));
			}
			result.put(loophead, disjuncts);
			mLogger.debug("Loop preprocessed");
		}
		return result;
	}

	private UnmodifiableTransFormula preProcessing(final String option, final UnmodifiableTransFormula loopRelation) {
		switch (option) {
		case "mod":
			return moduloTransformation(loopRelation);
		/*
		 * Disabled as it lead to unsound results by forcing underapproximation.
		 */
		// case "not":
		// return notTransformation(loopRelation);
		case "div":
			return divisionTransformation(loopRelation);
		default:
			break;
		}
		return loopRelation;
	}

	/**
	 * In case of modulo transformation we get a disjunction covering different cases of integer value intervals. For
	 * acceleration split these disjunctions for underapprox
	 *
	 * @param loopRelation
	 * @return
	 */
	private List<UnmodifiableTransFormula> splitDisjunction(final UnmodifiableTransFormula loopRelation) {
		final DNF dnfConverter = new DNF(mServices, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		final ModifiableTransFormula modTf =
				ModifiableTransFormulaUtils.buildTransFormula(loopRelation, mReplacementVarFactory, mScript);
		ModifiableTransFormula dnfModTf;
		try {
			dnfModTf = dnfConverter.process(mScript, modTf);
		} catch (final TermException e) {
			e.printStackTrace();
			throw new UnsupportedOperationException("Could not turn into DNF");
		}
		final List<UnmodifiableTransFormula> result = new ArrayList<>();
		final ApplicationTerm dnfAppTerm = (ApplicationTerm) dnfModTf.getFormula();
		if (dnfAppTerm.getFunction().getName() != "or") {
			result.add(loopRelation);
		} else {
			for (final Term disjunct : dnfAppTerm.getParameters()) {
				final TransFormulaBuilder tfb = new TransFormulaBuilder(loopRelation.getInVars(),
						loopRelation.getOutVars(), true, null, true, null, false);
				tfb.setFormula(disjunct);
				tfb.addAuxVarsButRenameToFreshCopies(loopRelation.getAuxVars(), mScript);
				tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
				result.add(tfb.finishConstruction(mScript));
			}
		}
		return result;
	}

	/**
	 * Rewrite not formulas such as != and not(< x y)
	 *
	 * @param loopRelation
	 * @return
	 */
	private UnmodifiableTransFormula notTransformation(final UnmodifiableTransFormula loopRelation) {
		mLogger.debug("Transforming not");
		final ModifiableTransFormula modTf =
				ModifiableTransFormulaUtils.buildTransFormula(loopRelation, mReplacementVarFactory, mScript);
		final RemoveNegation rn = new RemoveNegation();
		final RewriteDisequality rd = new RewriteDisequality();
		ModifiableTransFormula negFreeTf;
		try {
			negFreeTf = rn.process(mScript, modTf);
			negFreeTf = rd.process(mScript, negFreeTf);
		} catch (final TermException e) {
			mLogger.debug("Could not deal with not");
			negFreeTf = null;
			e.printStackTrace();
		}
		return buildFormula(loopRelation, negFreeTf.getFormula());
	}

	/**
	 * substitute modulo by a disjunction
	 *
	 * @param loopRelation
	 * @return
	 */
	private UnmodifiableTransFormula moduloTransformation(final UnmodifiableTransFormula loopRelation) {
		mLogger.debug("Transforming modulo");
		final ModifiableTransFormula modTf =
				ModifiableTransFormulaUtils.buildTransFormula(loopRelation, mReplacementVarFactory, mScript);
		final ModuloNeighborTransformation modNeighborTransformer = new ModuloNeighborTransformation(mServices, true);
		ModifiableTransFormula modTfTransformed;
		try {
			modTfTransformed = modNeighborTransformer.process(mScript, modTf);
		} catch (final TermException e) {
			mLogger.debug("Could not deal with modulo");
			modTfTransformed = null;
			e.printStackTrace();
		}
		/*
		 * TODO: programs with multiple modulos Use SubTermPropertyChecker -> returns multiple terms
		 */

		final List<Term> result = new ArrayList<>();
		final ApplicationTermFinder applicationTermFinder = new ApplicationTermFinder("mod", false);
		if (modTfTransformed != null) {
			final ApplicationTerm modAppTermTransformed = (ApplicationTerm) modTfTransformed.getFormula();
			for (final Term param : modAppTermTransformed.getParameters()) {
				if (applicationTermFinder.findMatchingSubterms(param).isEmpty()) {
					result.add(param);
				}
			}
		}
		final Term disjunctionNoMod = SmtUtils.or(mScript.getScript(), result);
		return buildFormula(loopRelation, disjunctionNoMod);
	}

	/**
	 * Rewrite division
	 *
	 * @param loopRelation
	 * @return
	 */
	private UnmodifiableTransFormula divisionTransformation(final UnmodifiableTransFormula loopRelation) {
		mLogger.debug("Transforming division");
		final ModifiableTransFormula modTf =
				ModifiableTransFormulaUtils.buildTransFormula(loopRelation, mReplacementVarFactory, mScript);
		final RewriteDivision rd = new RewriteDivision(mReplacementVarFactory);
		ModifiableTransFormula divModTf;
		try {
			divModTf = rd.process(mScript, modTf);
		} catch (final TermException e) {
			mLogger.debug("Could not deal with division");
			divModTf = null;
			e.printStackTrace();
		}
		return buildFormula(loopRelation, divModTf.getFormula());
	}

	private UnmodifiableTransFormula buildFormula(final UnmodifiableTransFormula origin, final Term term) {
		final TransFormulaBuilder tfb =
				new TransFormulaBuilder(origin.getInVars(), origin.getOutVars(), true, null, true, null, false);
		tfb.setFormula(term);
		tfb.addAuxVarsButRenameToFreshCopies(origin.getAuxVars(), mScript);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(mScript);
	}
}