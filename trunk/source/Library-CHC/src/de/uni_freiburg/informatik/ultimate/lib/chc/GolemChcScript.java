/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE CHC Library.
 *
 * The ULTIMATE CHC Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CHC Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CHC Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CHC Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CHC Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.chc;

import java.io.File;
import java.io.IOException;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Executor;

public class GolemChcScript implements IChcScript {
	private static final boolean ADD_CLAUSE_NAMES = false;
	private static final boolean ADD_COMMENTS = false;
	private static final boolean DECLARE_FUNCTIONS = true;

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mMgdScript;
	private final long mDefaultQueryTimeout;

	private boolean mProduceModels = false;

	private LBool mLastResult;
	private Model mLastModel = null;

	public GolemChcScript(final IUltimateServiceProvider services, final ManagedScript mgdScript) {
		this(services, mgdScript, -1L);
	}

	public GolemChcScript(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final long defaultTimeout) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(getClass());
		mMgdScript = mgdScript;
		mDefaultQueryTimeout = defaultTimeout;
	}

	@Override
	public Script getScript() {
		return mMgdScript.getScript();
	}

	@Override
	public LBool solve(final HcSymbolTable symbolTable, final List<HornClause> system) {
		return solve(symbolTable, system, -1L);
	}

	@Override
	public LBool solve(final HcSymbolTable symbolTable, final List<HornClause> system, final long timeout) {
		// generate file with Horn clauses
		final File tmpFile;
		try {
			tmpFile = File.createTempFile("golem_", ".smt2");
			mLogger.info("Writing script to file " + tmpFile.getAbsolutePath());

			final var dumperScript = new LoggingScript(tmpFile.getAbsolutePath(), false);
			dumperScript.setLogic(Logics.HORN);

			new ChcAsserter(mMgdScript, dumperScript, ADD_CLAUSE_NAMES, ADD_COMMENTS, DECLARE_FUNCTIONS)
					.assertClauses(symbolTable, system);
			dumperScript.checkSat();

			dumperScript.exit();
		} catch (final IOException e) {
			throw new RuntimeException(e);
		}

		try {
			// run golem on file
			final var executor = new Executor(getCommand(tmpFile), mMgdScript.getScript(), mLogger, mServices, "golem",
					null, null, null, determineTimeout(timeout));

			mLastResult = executor.parseCheckSatResult();
			mLastModel = (mLastResult == LBool.SAT && mProduceModels) ? executor.parseGetModelResult() : null;

			return mLastResult;

		} catch (final IOException e) {
			throw new RuntimeException(e);
		}
	}

	private String getCommand(final File file) {
		var command = "golem";
		if (mProduceModels) {
			command += " --print-witness";
		}
		return command + " " + file.getAbsolutePath();
	}

	@Override
	public boolean supportsModelProduction() {
		return true;
	}

	@Override
	public void produceModels(final boolean enable) {
		mProduceModels = enable;
	}

	@Override
	public Optional<Model> getModel() {
		if (mLastResult != LBool.SAT) {
			throw new UnsupportedOperationException("No model available: last query was " + mLastResult);
		}
		return Optional.ofNullable(mLastModel);
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
		return false;
	}

	@Override
	public void produceUnsatCores(final boolean enable) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Optional<Set<HornClause>> getUnsatCore() {
		throw new UnsupportedOperationException();
	}

	private long determineTimeout(final long queryTimeout) {
		final var globalTimeout = mServices.getProgressMonitorService().remainingTime();
		final var currentTimeout = queryTimeout <= 0 ? mDefaultQueryTimeout : queryTimeout;
		final var actualTimeout = currentTimeout <= 0 ? globalTimeout : Long.min(currentTimeout, globalTimeout);
		return actualTimeout;
	}
}
