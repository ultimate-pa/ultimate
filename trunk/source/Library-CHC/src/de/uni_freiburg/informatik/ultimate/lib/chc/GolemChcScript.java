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

import java.io.IOException;
import java.io.InputStreamReader;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.util.MonitoredProcess;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

public class GolemChcScript implements IChcScript {
	// TODO
	private static final String SCRIPT_PATH = "/tmp/golem-script.smt2";

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;

	private boolean mProduceModels = false;

	public GolemChcScript(final IUltimateServiceProvider services, final ManagedScript mgdScript) {
		mServices = services;
		mMgdScript = mgdScript;
	}

	@Override
	public Script getScript() {
		return mMgdScript.getScript();
	}

	@Override
	public LBool solve(final HcSymbolTable symbolTable, final List<HornClause> system) {
		// generate file with Horn clauses
		try {
			final var dumperScript = new LoggingScript(SCRIPT_PATH, false);
			dumperScript.setLogic(Logics.HORN);

			new ChcAsserter(mMgdScript, dumperScript, false, false).assertClauses(symbolTable, system);

			dumperScript.exit();
		} catch (final IOException e) {
			throw new IllegalStateException(e);
		}

		try {
			// run golem on file
			final var golem = MonitoredProcess.exec(getCommand(), null, mServices);
			golem.setTerminationAfterTimeout(0);

			// TODO parse output
			final var stdout = golem.getInputStream();
			final var stdoutReader = new InputStreamReader(stdout);
			stdoutReader.read();

			throw new UnsupportedOperationException();

		} catch (final IOException e) {
			throw new IllegalStateException(e);
		}
	}

	@Override
	public LBool solve(final HcSymbolTable symbolTable, final List<HornClause> system, final long timeout) {
		// TODO golem.setCountdownToTermination(timeout);
		throw new UnsupportedOperationException();
	}

	private String getCommand() {
		var command = "golem";
		if (mProduceModels) {
			command += " --print-witness";
		}
		return command + " " + SCRIPT_PATH;
	}

	@Override
	public boolean supportsModelProduction() {
		// TODO
		return false;
	}

	@Override
	public void produceModels(final boolean enable) {
		mProduceModels = enable;
		// TODO
		throw new UnsupportedOperationException();
	}

	@Override
	public Optional<Model> getModel() {
		// TODO
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
}
