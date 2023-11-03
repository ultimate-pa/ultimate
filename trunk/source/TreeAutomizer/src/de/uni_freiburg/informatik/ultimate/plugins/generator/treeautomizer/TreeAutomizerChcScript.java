/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE TreeAutomizer plug-in.
 *
 * The ULTIMATE TreeAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TreeAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TreeAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TreeAutomizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer;

import java.util.List;
import java.util.Optional;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.chc.Derivation;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornAnnot;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.chc.IChcScript;
import de.uni_freiburg.informatik.ultimate.lib.chc.results.ChcSatResult;
import de.uni_freiburg.informatik.ultimate.lib.chc.results.ChcUnsatResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph.TreeAutomizerCEGAR;

public class TreeAutomizerChcScript implements IChcScript {
	private static final String DUMMY_FILENAME = TreeAutomizerChcScript.class.getSimpleName();

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;
	private final TAPreferences mPrefs;
	private final ILogger mLogger;

	private boolean mProduceUnsatCores = false;

	private LBool mLastResult = null;
	private Set<HornClause> mUnsatCore;

	public TreeAutomizerChcScript(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final TAPreferences prefs) {
		mServices = services;
		mMgdScript = mgdScript;
		mPrefs = prefs;

		mLogger = mServices.getLoggingService().getLogger(TreeAutomizerChcScript.class);
	}

	@Override
	public Script getScript() {
		return mMgdScript.getScript();
	}

	@Override
	public LBool solve(final HcSymbolTable symbolTable, final List<HornClause> system) {
		return solve(mServices, symbolTable, system);
	}

	@Override
	public LBool solve(final HcSymbolTable symbolTable, final List<HornClause> system, final long timeout) {
		final var timer = mServices.getProgressMonitorService().getChildTimer(timeout);
		final var services = mServices.getProgressMonitorService().registerChildTimer(mServices, timer);
		return solve(services, symbolTable, system);
	}

	private LBool solve(final IUltimateServiceProvider services, final HcSymbolTable symbolTable,
			final List<HornClause> system) {
		reset();

		// TODO missing parameter: category info
		final var annot = new HornAnnot(DUMMY_FILENAME, mMgdScript, symbolTable, system, true, null);
		final var cegar = new TreeAutomizerCEGAR(services, annot, mPrefs, mLogger);
		try {
			final var result = cegar.iterate();
			mLastResult = resultToLBool(result);
			return mLastResult;
		} catch (final AutomataLibraryException e) {
			throw new IllegalStateException(e);
		}
	}

	private LBool resultToLBool(final IResult result) {
		if (result instanceof ChcSatResult) {
			return LBool.SAT;
		}
		if (result instanceof ChcUnsatResult) {
			if (mProduceUnsatCores) {
				mUnsatCore = ((ChcUnsatResult) result).getUnsatCore();
			}
			return LBool.UNSAT;
		}
		if (result instanceof TimeoutResult) {
			return LBool.UNKNOWN;
		}
		throw new IllegalArgumentException("Unknown result type: " + result.getClass());
	}

	@Override
	public boolean supportsModelProduction() {
		// TODO TreeAutomizer seems to produce some kind model, but just logs it (instead of returning it)
		return false;
	}

	@Override
	public void produceModels(final boolean enable) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Optional<Model> getModel() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean supportsDerivationProduction() {
		return false;
	}

	@Override
	public void produceDerivations(final boolean enable) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Optional<Derivation> getDerivation() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean supportsUnsatCores() {
		return true;
	}

	@Override
	public void produceUnsatCores(final boolean enable) {
		mProduceUnsatCores = enable;
	}

	@Override
	public Optional<Set<HornClause>> getUnsatCore() {
		if (mLastResult != LBool.UNSAT) {
			throw new UnsupportedOperationException("No UNSAT core available: last query was " + mLastResult);
		}
		return Optional.ofNullable(mUnsatCore);
	}

	private void reset() {
		mUnsatCore = null;
	}
}
