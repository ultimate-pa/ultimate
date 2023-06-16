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

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.ModelDescription;

/**
 * Used to access a constraint Horn solver via the {@link Script} interface. This can e.g. be used to access Z3's CHC
 * engine, Spacer.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class SmtChcScript implements IChcScript, AutoCloseable {
	private static final boolean ADD_COMMENTS = false;

	// We assume the function symbols are already declared in the script, as the Horn clause terms use the same script.
	// To support different scripts for creating and solving Horn clauses, we would have to transfer terms and declare
	// the necessary function symbols.
	private static final boolean DECLARE_FUNCTIONS = false;

	private final ManagedScript mMgdScript;
	private boolean mProduceModels;
	private boolean mProduceUnsatCores;

	private ChcTransferrer mTransferrer;
	private Map<String, HornClause> mName2Clause;

	public SmtChcScript(final ManagedScript mgdScript) {
		mMgdScript = mgdScript;
		mMgdScript.lock(this);
	}

	@Override
	public Script getScript() {
		return mMgdScript.getScript();
	}

	@Override
	public LBool solve(final HcSymbolTable symbolTable, final List<HornClause> system) {
		reset();
		mMgdScript.unlock(this);

		final List<HornClause> assertedSystem;
		if (mMgdScript == symbolTable.getManagedScript()) {
			assertedSystem = system;
		} else {
			mTransferrer = new ChcTransferrer(symbolTable.getManagedScript().getScript(), mMgdScript, symbolTable);
			assertedSystem = system.stream().map(mTransferrer::transfer).collect(Collectors.toList());
		}

		final var asserter =
				new ChcAsserter(mMgdScript, getScript(), mProduceUnsatCores, ADD_COMMENTS, DECLARE_FUNCTIONS);
		asserter.assertClauses(symbolTable, assertedSystem);
		mMgdScript.lock(this);

		mName2Clause = asserter.getName2Clause();

		return mMgdScript.checkSat(this);
	}

	@Override
	public LBool solve(final HcSymbolTable symbolTable, final List<HornClause> system, final long timeout) {
		mMgdScript.getScript().setOption(":timeout", timeout);
		try {
			return solve(symbolTable, system);
		} finally {
			try {
				// reset timeout
				mMgdScript.getScript().setOption(":timeout", 0L);
			} catch (final Throwable e) {
				// swallow exception
				e.printStackTrace();
			}
		}
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
		final var model = getScript().getModel();
		if (model == null) {
			return Optional.empty();
		}

		// back-transfer model if necessary
		final Model transferredModel;
		final Script outputScript;
		if (mTransferrer == null) {
			transferredModel = model;
			outputScript = getScript();
		} else {
			transferredModel = mTransferrer.transferBack(model);
			outputScript = mTransferrer.getSourceScript();
		}

		// ensure Ultimate normal form
		final var normalizedModel =
				new ChcSolutionNormalizer(outputScript).normalize((ModelDescription) transferredModel);
		return Optional.of(normalizedModel);
	}

	@Override
	public boolean supportsDerivationProduction() {
		return false;
	}

	@Override
	public void produceDerivations(final boolean enable) {
		throw new UnsupportedOperationException("Derivations are not supported");
	}

	@Override
	public Optional<Derivation> getDerivation() {
		throw new UnsupportedOperationException("Derivations are not supported");
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
		final var core = mMgdScript.getUnsatCore(this);
		final var result = new HashSet<HornClause>();
		for (final var term : core) {
			assert term instanceof ApplicationTerm : "Expected only term names in UNSAT core, but got " + term;
			final var name = ((ApplicationTerm) term).getFunction().getName();
			final var assertedClause = mName2Clause.get(name);
			final var originalClause =
					mTransferrer == null ? assertedClause : mTransferrer.transferBack(assertedClause);
			result.add(originalClause);
		}
		return Optional.of(result);
	}

	private void reset() {
		mName2Clause = null;
		mTransferrer = null;

		getScript().reset();
		getScript().setLogic(Logics.HORN);
		getScript().setOption(SMTLIBConstants.PRODUCE_MODELS, mProduceModels);
		getScript().setOption(SMTLIBConstants.PRODUCE_UNSAT_CORES, mProduceUnsatCores);
	}

	@Override
	public void close() throws Exception {
		reset();
		mMgdScript.unlock(this);
	}
}
