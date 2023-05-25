/*
 * Copyright (C) 2019 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgToChc plug-in.
 *
 * The ULTIMATE IcfgToChc plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgToChc plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgToChc plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgToChc plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgToChc plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc;

import java.util.ArrayList;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.chc.ChcCategorizer;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornAnnot;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClauseAST;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgSummaryTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.SemanticIndependenceConditionGenerator;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.SemanticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.ConcurrencyMode;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.IcfgLiptonReducer;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.ThreadModularHornClauseProvider;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.partialorder.ConditionSynthesizingIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.partialorder.ExplicitSymbolicIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.partialorder.ISymbolicIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.partialorder.SleepSetThreadModularHornClauseProvider;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.preferences.IcfgToChcPreferences;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class IcfgToChcObserver extends BaseObserver {
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final IcfgToChcPreferences mPrefs;

	private IElement mResult;

	public IcfgToChcObserver(final ILogger logger, final IUltimateServiceProvider services,
			final IcfgToChcPreferences prefs) {
		mLogger = logger;
		mServices = services;
		mPrefs = prefs;
	}

	public IElement getModel() {
		return mResult;
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean process(final IElement root) throws Exception {
		if (root instanceof IIcfg) {
			processIcfg((IIcfg<IcfgLocation>) root);
			return false;
		}
		return true;
	}

	private void processIcfg(final IIcfg<IcfgLocation> icfg) {
		final ManagedScript mgdScript = icfg.getCfgSmtToolkit().getManagedScript();
		final HcSymbolTable hcSymbolTable = new HcSymbolTable(mgdScript);
		final Collection<HornClause> resultChcs = getHornClauses(icfg, mgdScript, hcSymbolTable);

		final var chcCategoryInfo = ChcCategorizer.categorize(resultChcs, mgdScript);
		assert !chcCategoryInfo.containsNonLinearHornClauses() || isReturnReachable(icfg)
				|| !IcfgUtils.getForksInLoop(icfg).isEmpty()
				|| mPrefs.concurrencyMode() == ConcurrencyMode.PARAMETRIC : "Unexpected non-linear clauses";

		final var bad = resultChcs.stream()
				.filter(chc -> chc.constructFormula(mgdScript, false).getFreeVars().length != 0).findAny();
		assert bad.isEmpty() : bad;

		final HornAnnot annot = new HornAnnot(icfg.getIdentifier(), mgdScript, hcSymbolTable,
				new ArrayList<>(resultChcs), true, chcCategoryInfo);

		mResult = HornClauseAST.create(annot);
		ModelUtils.copyAnnotations(icfg, mResult);
	}

	private static boolean isReturnReachable(final IIcfg<IcfgLocation> icfg) {
		return new IcfgEdgeIterator(icfg).asStream().anyMatch(IIcfgSummaryTransition.class::isInstance);
	}

	private Collection<HornClause> getHornClauses(IIcfg<IcfgLocation> icfg, final ManagedScript mgdScript,
			final HcSymbolTable hcSymbolTable) {
		if (mPrefs.concurrencyMode() == ConcurrencyMode.PARAMETRIC || IcfgUtils.isConcurrent(icfg)) {
			assert !isReturnReachable(icfg);
			if (mPrefs.useLiptonReduction()) {
				// TODO support LBE for parametric programs
				assert mPrefs.concurrencyMode() == ConcurrencyMode.SINGLE_MAIN_THREAD;

				// TODO support combination of LBE and sleep sets
				assert !mPrefs.useSleepSets();

				// Create 2 instances of every thread, to ensure the reduction checks mover properties of each thread
				// template against another copy of the same template.
				final int instanceCount = 2;

				icfg = new IcfgLiptonReducer(mServices, icfg, instanceCount).getResult();
			}

			if (mPrefs.useSleepSets()) {
				final var independence = getIndependence(icfg, mgdScript);
				return new SleepSetThreadModularHornClauseProvider(mServices, mgdScript, icfg, hcSymbolTable,
						independence, mPrefs).getClauses();
			}
			return new ThreadModularHornClauseProvider(mServices, mgdScript, icfg, hcSymbolTable, mPrefs).getClauses();
		}
		return new ChcProviderForCalls(mgdScript, hcSymbolTable).getHornClauses(icfg);
	}

	private ISymbolicIndependenceRelation<IAction> getIndependence(final IIcfg<?> icfg, final ManagedScript mgdScript) {
		final boolean symmetric = true;
		final var independence = new SemanticIndependenceRelation<>(mServices, mgdScript, false, symmetric);

		switch (mPrefs.conditionalIndependence()) {
		case OFF:
			return new ExplicitSymbolicIndependenceRelation<>(independence, mgdScript.getScript());
		case PRECOMPUTED_CONDITIONS:
			final var factory =
					new BasicPredicateFactory(mServices, mgdScript, icfg.getCfgSmtToolkit().getSymbolTable());
			final var generator = new SemanticIndependenceConditionGenerator(mServices, mgdScript, factory, symmetric);
			return new ConditionSynthesizingIndependenceRelation<>(independence, generator, mgdScript.getScript());
		}

		throw new AssertionError("Unknown conditional independence setting: " + mPrefs.conditionalIndependence());
	}
}
