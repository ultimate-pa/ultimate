/*
 * Copyright (C) 2015 Dirk Steinmetz
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.AddSymbols;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.DNF;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.MatchInOutVars;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RemoveNegation;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteBooleans;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteDivision;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteEquality;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteIte;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteStrictInequalities;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteTrueFalse;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteUserDefinedTypes;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.SimplifyPreprocessor;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TermException;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TransitionPreprocessor;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearTransition;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.InequalityConverter.NlaHandling;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.SmtSymbols;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.IReplacementVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;

/**
 * Class linearizing {@link UnmodifiableTransFormula}s. For improved performance and variable management, this class
 * keeps a cache of linearization results. Thus, this class should only be used in one single context at a time, to
 * ensure proper garbage collection.
 *
 * @author (mostly) Matthias Heizmann
 */
public class CachedTransFormulaLinearizer {

	private final IUltimateServiceProvider mServices;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final SmtSymbols mSmtSymbols;
	private final ReplacementVarFactory mReplacementVarFactory;
	private final CfgSmtToolkit mCsToolkit;
	private final Map<UnmodifiableTransFormula, LinearTransition> mCache;

	/**
	 * Constructs a cached TransFormula linearizer.
	 *
	 * @param services
	 *            Service provider to use
	 * @param csToolkit
	 *            SMT manager
	 * @author Matthias Heizmann
	 */
	public CachedTransFormulaLinearizer(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final SmtSymbols smtSymbols, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		mServices = services;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mCsToolkit = csToolkit;
		mReplacementVarFactory = new ReplacementVarFactory(csToolkit, false);
		mSmtSymbols = smtSymbols;
		mCache = new HashMap<>();
	}

	/**
	 * Performs a transformation, utilizing the cache if possible. If the given {@link UnmodifiableTransFormula} has not
	 * yet been linearized, the result will also get added to the cache.
	 *
	 * The input and the output of this transformation are related as follows. Let the input be a
	 * {@link UnmodifiableTransFormula} that represents a formula φ whose free variables are primed and unprimed
	 * versions of the {@link BoogieVars} x_1,...,x_n. The output is a {@link LinearTransition} that represent a formula
	 * ψ whose free variables are primed and unprimed versions of x_1,...,x_n and additionally primed and unprimed
	 * versions of a set {@link IReplacementVarOrConst}s y_1,...,y_m. If we replace for each
	 * {@link IReplacementVarOrConst} the corresponding primed and unprimed variables by primed and unprimed versions of
	 * the {@link IReplacementVarOrConst}'s definition the the resulting formula is logically equivalent to the formula
	 * φ.
	 *
	 * @param tf
	 *            transformula to transform
	 * @return transformed transformula
	 */
	public LinearTransition linearize(final UnmodifiableTransFormula tf) {
		LinearTransition result = mCache.get(tf);
		if (result == null) {
			result = makeLinear(tf);
			mCache.put(tf, result);
		}
		return result;
	}

	/**
	 * Performs a transformation.
	 *
	 * The input and the output of this transformation are related as follows. Let the input be a
	 * {@link UnmodifiableTransFormula} that represents a formula φ whose free variables are primed and unprimed
	 * versions of the {@link BoogieVars} x_1,...,x_n. The output is a {@link LinearTransition} that represent a formula
	 * ψ whose free variables are primed and unprimed versions of x_1,...,x_n and additionally primed and unprimed
	 * versions of a set {@link IReplacementVarOrConst}s y_1,...,y_m. If we replace for each
	 * {@link IReplacementVarOrConst} the corresponding primed and unprimed variables by primed and unprimed versions of
	 * the {@link IReplacementVarOrConst}'s definition the the resulting formula is logically equivalent to the formula
	 * φ.
	 *
	 * @author Matthias Heizmann
	 * @param tf
	 *            transformula to transform
	 * @return transformed transformula
	 */
	private LinearTransition makeLinear(final UnmodifiableTransFormula tf) {
		ModifiableTransFormula tflr = ModifiableTransFormulaUtils.buildTransFormula(tf, mReplacementVarFactory,
				mCsToolkit.getManagedScript());

		for (final TransitionPreprocessor tpp : getPreprocessors()) {
			try {
				tflr = tpp.process(mCsToolkit.getManagedScript(), tflr);
			} catch (final TermException e) {
				throw new RuntimeException(e);
			}
		}
		LinearTransition lt;
		try {
			lt = LinearTransition.fromTransFormulaLR(tflr, NlaHandling.EXCEPTION);
		} catch (final TermException e) {
			throw new RuntimeException(e);
		}
		return lt;
	}

	/**
	 * (Undocumented Method, do not touch)
	 *
	 * @author Matthias Heizmann
	 */
	private TransitionPreprocessor[] getPreprocessors() {
		return new TransitionPreprocessor[] { new MatchInOutVars(), new AddSymbols(mReplacementVarFactory, mSmtSymbols),
				new RewriteDivision(mReplacementVarFactory),
				new RewriteBooleans(mReplacementVarFactory, mCsToolkit.getManagedScript()), new RewriteIte(),
				new RewriteUserDefinedTypes(mReplacementVarFactory, mCsToolkit.getManagedScript()),
				new RewriteEquality(), new SimplifyPreprocessor(mServices, mSimplificationTechnique),
				new DNF(mServices, mXnfConversionTechnique),
				new SimplifyPreprocessor(mServices, mSimplificationTechnique), new RewriteTrueFalse(),
				new RemoveNegation(), new RewriteStrictInequalities(), };
	}

}
