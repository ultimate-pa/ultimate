/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.explicit;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.IBoogieSymbolTableVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.AbsIntBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.generic.LiteralCollection;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;

/**
 * This abstract domain stores a single value or top for each variable.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ExplicitValueDomain implements IAbstractDomain<ExplicitValueState, IcfgEdge> {

	private final ILogger mLogger;
	private final LiteralCollection mLiteralCollection;
	private final IUltimateServiceProvider mServices;
	private final BoogieIcfgContainer mRootAnnotation;
	private final BoogieSymbolTable mSymbolTable;

	private IAbstractStateBinaryOperator<ExplicitValueState> mWideningOperator;
	private NonrelationalPostOperator<ExplicitValueState, BaseExplicitValueValue> mPostOperator;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final IBoogieSymbolTableVariableProvider mBpl2SmtSymbolTable;

	public ExplicitValueDomain(final ILogger logger, final BoogieSymbolTable symbolTable,
			final LiteralCollection literalCollector, final IUltimateServiceProvider services,
			final BoogieIcfgContainer icfg, final IBoogieSymbolTableVariableProvider variableProvider) {
		mLogger = logger;
		mLiteralCollection = literalCollector;
		mServices = services;
		mCfgSmtToolkit = icfg.getCfgSmtToolkit();
		mRootAnnotation = icfg;
		mSymbolTable = symbolTable;
		mBpl2SmtSymbolTable = variableProvider;
	}

	@Override
	public ExplicitValueState createTopState() {
		return new ExplicitValueState(mLogger, false);
	}

	@Override
	public ExplicitValueState createBottomState() {
		return new ExplicitValueState(mLogger, true);
	}

	@Override
	public IAbstractStateBinaryOperator<ExplicitValueState> getWideningOperator() {
		if (mWideningOperator == null) {
			mWideningOperator = new ExplicitValueWideningOperator(mLiteralCollection);
		}
		return mWideningOperator;
	}

	@Override
	public NonrelationalPostOperator<ExplicitValueState, BaseExplicitValueValue> getPostOperator() {
		if (mPostOperator == null) {
			final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
			final int maxParallelStates = prefs.getInt(AbsIntPrefInitializer.LABEL_MAX_PARALLEL_STATES);
			final int maxRecursionDepth = prefs.getInt(AbsIntPrefInitializer.LABEL_MAX_EVALUATION_RECURSION_DETPH);
			final ExplicitValueEvaluator evaluator = new ExplicitValueEvaluator(mLogger, mSymbolTable,
					mBpl2SmtSymbolTable, maxParallelStates, maxRecursionDepth);
			mPostOperator = new ExplicitValuePostOperator(mLogger, mSymbolTable, mBpl2SmtSymbolTable, maxParallelStates,
					mRootAnnotation.getBoogie2SMT(), mCfgSmtToolkit, evaluator);
		}
		return mPostOperator;
	}

	@Override
	public boolean isAbstractable(final Term inputTerm) {
		return false;
	}

	@Override
	public void beforeFixpointComputation(final Object... objects) {
		for (final Object o : objects) {
			if (o instanceof AbsIntBenchmark) {
				@SuppressWarnings("unchecked")
				final AbsIntBenchmark<IcfgEdge> absIntBenchmark = (AbsIntBenchmark<IcfgEdge>) o;
				getPostOperator().setAbsIntBenchmark(absIntBenchmark);
			}
		}

	}
}
