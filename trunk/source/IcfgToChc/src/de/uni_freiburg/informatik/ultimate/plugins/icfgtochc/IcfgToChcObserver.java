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
import de.uni_freiburg.informatik.ultimate.lib.chc.ChcCategoryInfo;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornAnnot;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClauseAST;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgSummaryTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.TermClassifier;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.SemanticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.ConcurrencyMode;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.IcfgLiptonReducer;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.SleepSetThreadModularHornClauseProvider;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.ThreadModularHornClauseProvider;
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

		final boolean isReturnReachable = isReturnReachable(icfg);
		final boolean hasNonLinearClauses = isReturnReachable || !IcfgUtils.getForksInLoop(icfg).isEmpty()
				|| mPrefs.concurrencyMode() == ConcurrencyMode.PARAMETRIC;
		final ChcCategoryInfo chcCategoryInfo =
				new ChcCategoryInfo(getLogics(resultChcs, mgdScript), hasNonLinearClauses);

		final var bad = resultChcs.stream()
				.filter(chc -> chc.constructFormula(mgdScript, false).getFreeVars().length != 0).findAny();
		assert bad.isEmpty() : bad;

		final HornAnnot annot = new HornAnnot(icfg.getIdentifier(), mgdScript, hcSymbolTable,
				new ArrayList<>(resultChcs), true, chcCategoryInfo);

		mResult = HornClauseAST.create(annot);
		ModelUtils.copyAnnotations(icfg, mResult);
	}

	private static Logics getLogics(final Collection<HornClause> resultChcs, final ManagedScript mgdScript) {
		final TermClassifier termClassifierChcs = new TermClassifier();
		resultChcs.forEach(chc -> termClassifierChcs.checkTerm(chc.constructFormula(mgdScript, false)));
		final TermClassifier termClassifierConstraints = new TermClassifier();
		resultChcs.forEach(chc -> termClassifierConstraints.checkTerm(chc.getConstraintFormula()));

		boolean hasArrays = false;
		boolean hasReals = false;
		boolean hasInts = false;
		for (final String osn : termClassifierChcs.getOccuringSortNames()) {
			hasArrays |= osn.contains(SmtSortUtils.ARRAY_SORT);
			hasReals |= osn.contains(SmtSortUtils.REAL_SORT);
			hasInts |= osn.contains(SmtSortUtils.INT_SORT);
		}

		boolean hasArraysInConstraints = false;
		boolean hasRealsInConstraints = false;
		boolean hasIntsInConstraints = false;
		for (final String osn : termClassifierConstraints.getOccuringSortNames()) {
			hasArraysInConstraints |= osn.contains(SmtSortUtils.ARRAY_SORT);
			hasRealsInConstraints |= osn.contains(SmtSortUtils.REAL_SORT);
			hasIntsInConstraints |= osn.contains(SmtSortUtils.INT_SORT);
		}
		assert hasArrays == hasArraysInConstraints;
		assert hasReals == hasRealsInConstraints;
		assert hasInts == hasIntsInConstraints;

		final boolean hasQuantifiersInConstraints = !termClassifierConstraints.getOccuringQuantifiers().isEmpty();

		if (!hasArrays && hasInts && !hasReals && !hasQuantifiersInConstraints) {
			return Logics.QF_LIA;
		}
		if (!hasArrays && !hasInts && hasReals && !hasQuantifiersInConstraints) {
			return Logics.QF_LRA;
		}
		if (hasArrays && hasInts && !hasReals && !hasQuantifiersInConstraints) {
			return Logics.QF_ALIA;
		}
		// not a CHC-comp 2019 logic -- we don't care for more details right now
		return Logics.ALL;
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
				final var independence = new SemanticIndependenceRelation<>(mServices, mgdScript, false, true);
				return new SleepSetThreadModularHornClauseProvider(mServices, mgdScript, icfg, hcSymbolTable,
						independence, mPrefs).getClauses();
			}
			return new ThreadModularHornClauseProvider(mServices, mgdScript, icfg, hcSymbolTable, mPrefs).getClauses();
		}
		return new ChcProviderForCalls(mgdScript, hcSymbolTable).getHornClauses(icfg);
	}
}
