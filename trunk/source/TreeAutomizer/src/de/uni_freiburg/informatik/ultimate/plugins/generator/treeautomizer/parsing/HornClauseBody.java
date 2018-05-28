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
package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.parsing;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HCSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HcBodyVar;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HcHeadVar;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HornClausePredicateSymbol;
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
public class HornClauseBody {
	private final HornClauseCobody mCobody;
	private ApplicationTerm mHead;
	private final HornClauseParserScript mParserScript;

	/***
	 * Construct a Body of a Horn statement.
	 */
	public HornClauseBody(final HornClauseParserScript script) {
		mCobody = new HornClauseCobody(script);
		mParserScript = script;
	}

	/***
	 * Copy constructor
	 */
	public HornClauseBody(final HornClauseBody original) {
		mCobody = new HornClauseCobody(original.mCobody);
		mParserScript = original.mParserScript;
		mHead = original.mHead;
	}

	/***
	 * Add literal to the cobody.
	 * @param literal
	 */
	public void addPredicateToCobody(final ApplicationTerm literal) {
		mCobody.addPredicate(literal);
	}

	/***
	 * Convert the body to a HornClause.
	 * @param solverScript
	 * @param symbolTable
	 * @return
	 */
	public HornClause convertToHornClause(final ManagedScript solverScript, final HCSymbolTable symbolTable,
			final Script parserScript) {

		/*
		 *  register all HornClausePredicateSymbols --> this must be done before term transferral, because it declares
		 *  the functions in the solverScript
		 */
		final List<HornClausePredicateSymbol> cobodySymbols = mCobody.getPredicates(symbolTable);
		final HornClausePredicateSymbol bodySymbol = mHead == null ? null :
			symbolTable.getOrConstructHornClausePredicateSymbol(
				mHead.getFunction().getName(), mHead.getFunction().getParameterSorts());


		// transfer all terms
		{
			final TermTransferrer termTransferrer = new TermTransferrer(solverScript.getScript());
			mHead = mHead == null ? null : (ApplicationTerm) termTransferrer.transform(mHead);
			mCobody.transformTerms(termTransferrer::transform);
		}

		final Set<HcBodyVar> coBodyVars = normalizeVariables(symbolTable, solverScript);


		final List<List<Term>> cobodyArgs = mCobody.getPredicateToVars(symbolTable);

		if (mHead == null) {
			return new HornClause(solverScript, symbolTable,
				getTransitionFormula(parserScript),
				cobodySymbols,
				cobodyArgs,
				coBodyVars);
		}

		/*
		 * Collect the predicate symbol and the arguments of the body predicate from the Term mHead
		 *  right now we assume that
		 *   - all parameters of the head predicate are variables
		 *   - all parameters of the head predicate are pairwise different (i.e. there are no repeated variables)
		 *   TODO: lift this assumption by introducing equalities
		 */
//		final HornClausePredicateSymbol bodySymbol = symbolTable.getOrConstructHornClausePredicateSymbol(
//				mHead.getFunction().getName(), mHead.getFunction().getParameterSorts());
//		final List<TermVariable> parameterTermVariables = Arrays.asList(mHead.getParameters()).stream()
//				.map(t -> (TermVariable) t)
//				.collect(Collectors.toList());
//		assert parameterTermVariables.size() == new HashSet<>(parameterTermVariables).size() : "TODO: eliminate "
//				+ "duplicate arguments";
//		final List<TermVariable> bodyVars = parameterTermVariables;
		final List<HcHeadVar> bodyVars = symbolTable.getHcHeadVarsForPredSym(bodySymbol);

		return new HornClause(solverScript, symbolTable,
				getTransitionFormula(parserScript),
				bodySymbol,
				bodyVars,
				cobodySymbols,
				cobodyArgs,
				coBodyVars);
	}

	/**
	 * Bring the head predicate's arguments into normal form.
	 * (The variables are normalized according to their argument position and sort)
	 *
	 * @param symbolTable
	 * @param script
	 * @return
	 */
	private Set<HcBodyVar> normalizeVariables(final HCSymbolTable symbolTable, final ManagedScript solverScript) {

		final Set<HcBodyVar> bodyVars = new HashSet<>();
		final String headPredSymbolName = mHead == null ?
							symbolTable.getMethodNameForPredSymbol(symbolTable.getFalseHornClausePredicateSymbol()) :
							symbolTable.getMethodNameForPredSymbol(mHead.getFunction());

		// normalize head variables
		final Map<Term, Term> subs = new HashMap<>();
		if (mHead != null) {
//			final Term[] newHeadParams = new Term[mHead.getParameters().length];
			for (int i = 0; i < mHead.getParameters().length; i++) {
				final TermVariable pTv = (TermVariable) mHead.getParameters()[i];
				final Sort sort = pTv.getSort();

				final HcHeadVar headVar = symbolTable.getOrConstructHeadVar(headPredSymbolName, i, sort);

				subs.put(pTv, headVar.getTermVariable());
//				newHeadParams[i] = headVar.getTermVariable();
			}

//			mHead = (ApplicationTerm) mParserScript.term(mHead.getFunction().getName(), newHeadParams);
			// note: it does not seem to matter much, which script we pass here
			mHead = (ApplicationTerm) new Substitution(solverScript, subs).transform(mHead);

		}
		// normalize (co)body variables
		int counter = 1;
		for (final TermVariable tv : mCobody.getVariables()) {
			if (subs.containsKey(tv)) {
				// head var, already normalized, skip it
				continue;
			}

			final HcBodyVar bodyVar = symbolTable.getOrConstructBodyVar(headPredSymbolName,
					counter++, tv.getSort());

			subs.put(tv, bodyVar.getTermVariable());
			bodyVars.add(bodyVar);

		}
		mCobody.applySubstitution(subs);
		return bodyVars;
	}

	/***
	 * Set the head literal of the body.
	 * @param literal
	 * @return
	 */
	public boolean setHead(final ApplicationTerm literal) {
		if (mHead == null) {
//			final Map<Term, Term> subs = new HashMap<>();
//			for (final Term param : literal.getParameters()) {
//				if (param instanceof TermVariable) {
//					// variables are the standard case --> do nothing
//					continue;
//				}
//				if (subs.containsKey(param)) {
//					// already saw this parameter --> we already substitute it --> do nothing
//					continue;
//				}
//				final TermVariable freshTv = mParserScript.createFreshTermVariable("fresh", param.getSort());
//				subs.put(param, freshTv);
//				addTransitionFormula(SmtUtils.binaryEquality(mParserScript, param, freshTv));
//			}
//			mHead = (ApplicationTerm) new Substitution(mParserScript, subs).transform(literal);

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
	 * Merge the cobody of the body with the given cobody.
	 */
	public void mergeCobody(final HornClauseCobody cobody) {
		this.mCobody.mergeCobody(cobody);
	}

	/***
	 * Add the transition formula to the cobody (can be called several times).
	 * @param formula
	 */
	public void addTransitionFormula(final Term formula) {
		mCobody.addTransitionFormula(formula);
	}

	@Override
	public String toString() {
		return '(' + mCobody.toString() + " ==> " + (mHead == null ? "false" : mHead.toString()) + ')';
	}

//	private Map<HornClausePredicateSymbol, List<TermVariable>> getBodyPredicateToVars(
//			final HCSymbolTable symbolTable) {
//
//		final HashMap<HornClausePredicateSymbol, List<TermVariable>> res = new HashMap<>();
//		if (mHead != null) {
//			final ArrayList<TermVariable> vars = new ArrayList<>();
//			for (final Term par : mHead.getParameters()) {
//				vars.add((TermVariable) par);
//			}
//
//			res.put(symbolTable.getOrConstructHornClausePredicateSymbol(
//						mHead.getFunction().getName(), mHead.getFunction().getParameterSorts()),
//					vars);
//		}
//		return res;
//	}



//	/***
//	 * Get the cobody
//	 * @param symbolTable
//	 * @return
//	 */
//	public Map<HornClausePredicateSymbol, List<TermVariable>> getCobodyPredicateToVars(
//			HCSymbolTable symbolTable) {
//		return mCobody.getPredicateToVars(symbolTable);
//	}

	/***
	 * Get the transition formula.
	 * @param script
	 * @return
	 */
	public Term getTransitionFormula(final Script parserScript) {
		return mCobody.getTransitionFormula(parserScript);
	}
}
