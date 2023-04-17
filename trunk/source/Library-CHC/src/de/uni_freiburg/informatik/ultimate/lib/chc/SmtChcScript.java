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

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.NamedTermWrapper;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
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
// TODO avoid code duplication between this class and ChcSmtPrinterObserver
public class SmtChcScript implements IChcScript {

	private final ManagedScript mMgdScript;
	private boolean mProduceUnsatCores;
	private Map<String, HornClause> mName2Clause;

	public SmtChcScript(final ManagedScript mgdScript) {
		mMgdScript = mgdScript;
		mMgdScript.lock(this);
		mMgdScript.getScript().setLogic(Logics.HORN);
	}

	@Override
	public Script getScript() {
		return mMgdScript.getScript();
	}

	@Override
	public LBool solve(final HcSymbolTable symbolTable, final List<HornClause> system) {
		reset();

		// TODO extract and declare functions -- should we take a HcSymbolTable?

		// translate clauses to SMT and assert them
		for (final var clause : system) {
			final var term = clause.constructFormula(mMgdScript, mProduceUnsatCores);
			mMgdScript.assertTerm(this, term);

			// record name mapping for backtranslation later
			if (mProduceUnsatCores) {
				final var namedTerm = new NamedTermWrapper(term);
				assert namedTerm.isNamed();
				mName2Clause.put(namedTerm.getName(), clause);
			}
		}

		return mMgdScript.checkSat(this);
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
	public Model getModel() {
		return getScript().getModel();
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
	public Derivation getDerivation() {
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
	public Set<HornClause> getUnsatCore() {
		final var core = mMgdScript.getUnsatCore(this);
		final var result = new HashSet<HornClause>();
		for (final var term : core) {
			final var namedTerm = new NamedTermWrapper(term);
			assert namedTerm.isNamed();
			result.add(mName2Clause.get(namedTerm.getName()));
		}
		return result;
	}

	private void reset() {
		mName2Clause = new HashMap<>();
	}
}
