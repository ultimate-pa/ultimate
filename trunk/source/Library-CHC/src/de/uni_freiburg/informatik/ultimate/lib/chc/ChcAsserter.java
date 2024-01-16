/*
 * Copyright (C) 2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2018-2023 University of Freiburg
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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.NamedTermWrapper;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Issues assert commands for CHC clauses to a {@link Script}.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class ChcAsserter {
	private final ManagedScript mMgdScript;
	private final Script mOutputScript;

	private final boolean mAddClauseNames;
	private final boolean mAddComments;
	private final boolean mDeclareFunctions;

	private Map<String, HornClause> mName2Clause;

	/**
	 *
	 * @param mgdScript
	 *            A {@link ManagedScript} used to generate SMT terms from the Horn clauses
	 * @param outputScript
	 *            The script to which function declarations and assert commands are issued
	 * @param addClauseNames
	 *            Set to true to generate named terms, e.g. for UNSAT core support
	 * @param addComments
	 *            Set to true to output comments describing Horn clauses. This is only supported if {@code script} is a
	 *            {@link LoggingScript}.
	 */
	public ChcAsserter(final ManagedScript mgdScript, final Script outputScript, final boolean addClauseNames,
			final boolean addComments, final boolean declareFunctions) {
		mMgdScript = mgdScript;
		mOutputScript = outputScript;
		mAddClauseNames = addClauseNames;
		mAddComments = addComments;
		mDeclareFunctions = declareFunctions;

		assert !mAddComments || outputScript instanceof LoggingScript;
	}

	public void assertClauses(final HcSymbolTable symbolTable, final List<HornClause> clauses) {
		reset();

		// do some categorisation of the clauses
		final List<HornClause> rules = new ArrayList<>();
		final List<HornClause> queries = new ArrayList<>();
		for (final HornClause hc : clauses) {
			if (hc.isHeadFalse()) {
				queries.add(hc);
			} else {
				rules.add(hc);
			}
		}

		// declare functions
		if (mDeclareFunctions) {
			for (final HcPredicateSymbol hcPred : symbolTable.getHcPredicateSymbols()) {
				final FunctionSymbol fsym = hcPred.getFunctionSymbol();
				mOutputScript.declareFun(fsym.getName(), fsym.getParameterSorts(), fsym.getReturnSort());
			}
			for (final Triple<String, Sort[], Sort> sf : symbolTable.getSkolemFunctions()) {
				mOutputScript.declareFun(sf.getFirst(), sf.getSecond(), sf.getThird());
			}
		}

		// assert constraints
		assertClauses(rules);
		assertClauses(queries);
	}

	private void assertClauses(final List<HornClause> clauses) {
		for (final HornClause hc : clauses) {
			if (mAddComments) {
				((LoggingScript) mOutputScript).comment(hc.toString());
			}
			final Term formula = hc.constructFormula(mMgdScript, mAddClauseNames);
			mOutputScript.assertTerm(formula);

			// record name mapping for backtranslation later
			if (mAddClauseNames) {
				final var namedTerm = NamedTermWrapper.of(formula);
				assert namedTerm != null : "term was not named: " + formula;
				mName2Clause.put(namedTerm.getName(), hc);
			}
		}
	}

	private void reset() {
		mName2Clause = new HashMap<>();
	}

	public Map<String, HornClause> getName2Clause() {
		return Collections.unmodifiableMap(mName2Clause);
	}
}