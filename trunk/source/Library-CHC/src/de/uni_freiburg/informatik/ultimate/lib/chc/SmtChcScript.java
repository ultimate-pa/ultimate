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

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

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
	private boolean mProduceUnsatCores;

	private boolean mIsPushed;
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
		mMgdScript.push(this, 1);
		mIsPushed = true;

		mMgdScript.unlock(this);
		final var asserter =
				new ChcAsserter(mMgdScript, getScript(), mProduceUnsatCores, ADD_COMMENTS, DECLARE_FUNCTIONS);
		asserter.assertClauses(symbolTable, system);
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
		getScript().setOption(SMTLIBConstants.PRODUCE_MODELS, enable);
	}

	@Override
	public Optional<Model> getModel() {
		return Optional.ofNullable(getScript().getModel());
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
		getScript().setOption(SMTLIBConstants.PRODUCE_UNSAT_CORES, enable);
		mProduceUnsatCores = enable;
	}

	@Override
	public Optional<Set<HornClause>> getUnsatCore() {
		final var core = mMgdScript.getUnsatCore(this);
		final var result = new HashSet<HornClause>();
		for (final var term : core) {
			assert term instanceof ApplicationTerm : "Expected only term names in UNSAT core, but got " + term;
			final var name = ((ApplicationTerm) term).getFunction().getName();
			result.add(mName2Clause.get(name));
		}
		return Optional.of(result);
	}

	private void reset() {
		mName2Clause = null;
		if (mIsPushed) {
			mMgdScript.pop(this, 1);
		}
	}

	@Override
	public void close() throws Exception {
		reset();
		mMgdScript.unlock(this);
	}
}
