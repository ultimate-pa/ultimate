/*
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Mostafa M.A. (mostafa.amin93@gmail.com)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TreeAutomizer Plugin.
 *
 * The ULTIMATE TreeAutomizer Plugin is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TreeAutomizer Plugin is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TreeAutomizer Plugin. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TreeAutomizer Plugin, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TreeAutomizer Plugin grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.source.smtparser.chc;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.chc.HcBodyVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcHeadVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * Body of a Horn clause according to our grammar for Horn clauses in SMTLib2.
 * Confusing terminology-warning:
 * Once the Horn clause is fixed (we make no more derivations in the grammar), we also call this the head.
 *
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class HornClauseHead {
	private final HornClauseBody mBody;
	private ApplicationTerm mHead;
	private final HornClauseParserScript mParserScript;

	/***
	 * Construct a Body of a Horn statement.
	 */
	public HornClauseHead(final HornClauseParserScript script) {
		mBody = new HornClauseBody(script);
		mParserScript = script;
	}

	/***
	 * Add literal to the cobody.
	 * @param literal
	 */
	public void addPredicateToBody(final ApplicationTerm literal) {
		mBody.addPredicate(literal);
	}

	/***
	 * Convert the body to a HornClause.
	 * @param solverScript
	 * @param symbolTable
	 * @return
	 */
	public HornClause convertToHornClause(final ManagedScript solverScript, final HcSymbolTable symbolTable,
			final Script parserScript) {

		/*
		 *  register all HornClausePredicateSymbols --> this must be done before term transferral, because it declares
		 *  the functions in the solverScript
		 */
		final HcPredicateSymbol headSymbol = mHead == null ? null :
			symbolTable.getOrConstructHornClausePredicateSymbol(mHead);
		final List<HcPredicateSymbol> bodySymbols = mBody.getPredicates(symbolTable);


		// transfer all terms
		{
			final TermTransferrer termTransferrer = new TermTransferrer(solverScript.getScript());
			mHead = mHead == null ? null : (ApplicationTerm) termTransferrer.transform(mHead);
			mBody.transformTerms(termTransferrer::transform);
		}

		final Set<HcVar> bodyVars = normalizeVariables(symbolTable, solverScript);


		final List<List<Term>> bodyArgs = mBody.getPredicateToVars(symbolTable);

		if (mHead == null) {
			return new HornClause(solverScript, symbolTable,
				getTransitionFormula(solverScript.getScript()),
				bodySymbols,
				bodyArgs,
				bodyVars);
		}

		final List<HcHeadVar> headVars = symbolTable.getHcHeadVarsForPredSym(headSymbol, false);

		return new HornClause(solverScript, symbolTable,
				getTransitionFormula(solverScript.getScript()),
				headSymbol,
				headVars,
				bodySymbols,
				bodyArgs,
				bodyVars);
	}

	/**
	 * Bring the head predicate's arguments into normal form.
	 * (The variables are normalized according to their argument position and sort)
	 *
	 * @param symbolTable
	 * @param script
	 * @return
	 */
	private Set<HcVar> normalizeVariables(final HcSymbolTable symbolTable, final ManagedScript solverScript) {

		final Set<HcVar> bodyVars = new HashSet<>();
		final HcPredicateSymbol headPredSymbolName = mHead == null ?
							symbolTable.getFalseHornClausePredicateSymbol() :
							symbolTable.getOrConstructHornClausePredicateSymbol(mHead);

		// normalize head variables
		final Map<Term, Term> subs = new HashMap<>();
		if (mHead != null) {
			for (int i = 0; i < mHead.getParameters().length; i++) {
				final TermVariable pTv = (TermVariable) mHead.getParameters()[i];
				final Sort sort = pTv.getSort();

				final HcHeadVar headVar = symbolTable.getOrConstructHeadVar(headPredSymbolName, i, sort);

				subs.put(pTv, headVar.getTermVariable());
			}

			// note: it does not seem to matter much, which script we pass here
			mHead = (ApplicationTerm) new Substitution(solverScript, subs).transform(mHead);

		}
		// normalize (co)body variables
		int counter = 1;
		for (final TermVariable tv : mBody.getVariables()) {
			if (subs.containsKey(tv)) {
				// head var, already normalized, skip it
				continue;
			}

			final HcBodyVar bodyVar = symbolTable.getOrConstructBodyVar(headPredSymbolName,
					counter++, tv.getSort());

			subs.put(tv, bodyVar.getTermVariable());
			bodyVars.add(bodyVar);

		}
		mBody.applySubstitution(subs);
		return bodyVars;
	}

	/***
	 * Set the head literal of the body.
	 * @param literal
	 * @return
	 */
	public boolean setHead(final ApplicationTerm literal) {
		if (mHead == null) {
			assert Arrays.asList(literal.getParameters()).stream().allMatch(p -> p instanceof TermVariable);
			assert Arrays.asList(literal.getParameters()).stream().collect(Collectors.toSet()).size()
				== literal.getParameters().length;
			mHead = literal;
			return true;
		} else {
			return false;
		}
	}

	/***
	 * Add the transition formula to the cobody (can be called several times).
	 * @param formula
	 */
	public void addTransitionFormula(final Term formula) {
		mBody.addTransitionFormula(formula);
	}

	@Override
	public String toString() {
		return '(' + mBody.toString() + " ==> " + (mHead == null ? "false" : mHead.toString()) + ')';
	}

	/***
	 * Get the transition formula.
	 * @param script
	 * @return
	 */
	public Term getTransitionFormula(final Script parserScript) {
		return mBody.getTransitionFormula(parserScript);
	}
}
