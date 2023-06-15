/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE ChcSolver plug-in.
 *
 * The ULTIMATE ChcSolver plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ChcSolver plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ChcSolver plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ChcSolver plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ChcSolver plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.chcsolver;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.chc.ChcSolution;
import de.uni_freiburg.informatik.ultimate.lib.chc.Derivation;
import de.uni_freiburg.informatik.ultimate.lib.chc.GolemChcScript;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornAnnot;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClauseAST;
import de.uni_freiburg.informatik.ultimate.lib.chc.IChcScript;
import de.uni_freiburg.informatik.ultimate.lib.chc.SmtChcScript;
import de.uni_freiburg.informatik.ultimate.lib.chc.eldarica.EldaricaChcScript;
import de.uni_freiburg.informatik.ultimate.lib.chc.results.ChcSatResult;
import de.uni_freiburg.informatik.ultimate.lib.chc.results.ChcUnknownResult;
import de.uni_freiburg.informatik.ultimate.lib.chc.results.ChcUnsatResult;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.chcsolver.preferences.ChcSolverPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.TreeAutomizerChcScript;

public class ChcSolverObserver extends BaseObserver {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ChcSolverPreferences mPrefs;

	private ChcSolution mSolution;

	public ChcSolverObserver(final IUltimateServiceProvider services, final ILogger logger,
			final ChcSolverPreferences prefs) {
		mServices = services;
		mLogger = logger;
		mPrefs = prefs;
	}

	@Override
	public boolean process(final IElement root) throws Throwable {
		if (!(root instanceof HornClauseAST)) {
			return true;
		}

		final HornAnnot annot = HornAnnot.getAnnotation(root);
		final IChcScript chcScript = getBackend(annot);
		configureBackend(chcScript);

		final var satisfiability = chcScript.solve(annot.getSymbolTable(), annot.getHornClauses());
		final IResult result = createResult(chcScript, satisfiability);
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);

		if (chcScript instanceof AutoCloseable) {
			((AutoCloseable) chcScript).close();
		}

		return false;
	}

	private IChcScript getBackend(final HornAnnot annotation) {
		switch (mPrefs.getBackend()) {
		case ELDARICA:
			return new EldaricaChcScript(mServices, annotation.getScript().getScript());
		case Z3:
			// We use the script given in the annotation. For this to work, that script should use Z3.
			// To use a fresh Z3 instance for solving instead, one has to transfer the Horn clause terms to that script.
			return new SmtChcScript(annotation.getScript());
		case TREEAUTOMIZER:
			// NOTE: TAPreferences (last parameter) currently unused by TreeAutomizer
			return new TreeAutomizerChcScript(mServices, annotation.getScript(), null);
		case GOLEM:
			return new GolemChcScript(mServices, annotation.getScript());
		default:
			throw new UnsupportedOperationException("Unsupported CHC backend: " + mPrefs.getBackend());
		}
	}

	private void configureBackend(final IChcScript backend) {
		if (backend.supportsModelProduction()) {
			backend.produceModels(mPrefs.produceModels());
		} else if (mPrefs.produceModels()) {
			mLogger.warn("Model production is not supported by backend");
		}

		if (backend.supportsDerivationProduction()) {
			backend.produceDerivations(mPrefs.produceDerivation());
		} else if (mPrefs.produceDerivation()) {
			mLogger.warn("Derivation production is not supported by backend");
		}

		if (backend.supportsUnsatCores()) {
			backend.produceUnsatCores(mPrefs.produceUnsatCore());
		} else if (mPrefs.produceUnsatCore()) {
			mLogger.warn("UNSAT core production is not supported by backend");
		}
	}

	private IResult createResult(final IChcScript chcScript, final LBool satisfiability) {
		switch (satisfiability) {
		case SAT:
			return createSatResult(chcScript);
		case UNSAT:
			return createUnSatResult(chcScript);
		case UNKNOWN:
			mSolution = ChcSolution.unknown();
			return new ChcUnknownResult(Activator.PLUGIN_ID, "CHC solver returned UNKNOWN.");
		default:
			throw new AssertionError("Unknown CHC result: " + satisfiability);
		}
	}

	private ChcSatResult createSatResult(final IChcScript chcScript) {
		final Model model;
		if (mPrefs.produceModels() && chcScript.supportsModelProduction()) {
			model = chcScript.getModel().orElse(null);
		} else {
			model = null;
		}
		mSolution = ChcSolution.sat(model);
		return new ChcSatResult(Activator.PLUGIN_ID, "The given horn clause set is SAT", model);
	}

	private ChcUnsatResult createUnSatResult(final IChcScript chcScript) {
		final Derivation derivation;
		if (mPrefs.produceDerivation() && chcScript.supportsDerivationProduction()) {
			derivation = chcScript.getDerivation().orElse(null);
		} else {
			derivation = null;
		}

		final Set<HornClause> core;
		if (mPrefs.produceUnsatCore() && chcScript.supportsUnsatCores()) {
			core = chcScript.getUnsatCore().orElse(null);
		} else {
			core = null;
		}

		mSolution = ChcSolution.unsat(derivation, core);
		return new ChcUnsatResult(Activator.PLUGIN_ID, "The given horn clause set is UNSAT", derivation, core);
	}

	public ChcSolution getSolution() {
		return mSolution;
	}
}
