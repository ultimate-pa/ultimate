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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HCSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HornClausePredicateSymbol;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;

/**
 * Body of a Horn clause according to our grammar for Horn clauses in SMTLib2.
 * Once the Horn clause is fixed (we make no more derivations in the grammar), we also call this the body of the Horn
 * clause.
 *
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class HornClauseCobody {
	private final Set<Term> mTransitions;
	private final List<ApplicationTerm> mPredicates;

	private boolean mFinalized = false;

	private final List<HornClausePredicateSymbol> mPredicateSymbols;
	private final List<List<TermVariable>> mPredicateSymbolToVariables;

	private final HornClauseParserScript mParserScript;

	/***
	 * Constructor of the cobody of a horn statement.
	 * @param parserScript
	 */
	public HornClauseCobody(final HornClauseParserScript parserScript) {
		mPredicates = new ArrayList<>();
		mPredicateSymbols = new ArrayList<>();
		mPredicateSymbolToVariables = new ArrayList<>();
		mTransitions = new HashSet<>();
		mParserScript = parserScript;
	}

	/**
	 *
	 * @param original
	 */
	public HornClauseCobody(final HornClauseCobody original) {
		mPredicates = new ArrayList<>(original.mPredicates);
		mPredicateSymbols = new ArrayList<>(original.mPredicateSymbols);
		mPredicateSymbolToVariables = new ArrayList<>();
		for (final List<TermVariable> l : original.mPredicateSymbolToVariables) {
			mPredicateSymbolToVariables.add(new ArrayList<>(l));
		}
		mTransitions = new HashSet<>(original.mTransitions);
		mParserScript = original.mParserScript;
	}

	/***
	 * Add a literal predicate to the cobody.
	 * @param literal
	 */
	public void addPredicate(final ApplicationTerm literal) {
		assert !mFinalized;
		mPredicates.add(literal);
	}

	/***
	 * Add a transition formula to the cobody (can be called several times, a conjunction will be built).
	 * @param formula
	 */
	public void addTransitionFormula(final Term formula) {
		assert !mFinalized;
		mTransitions.add(formula);
	}

	/***
	 * Merge with a different cobody, the results is stored in @this.
	 * @param cobody
	 */
	public void mergeCobody(final HornClauseCobody cobody) {
		assert !mFinalized;
		for (final ApplicationTerm predicate : cobody.mPredicates) {
			addPredicate(predicate);
		}
		for (final Term transition : cobody.mTransitions) {
			addTransitionFormula(transition);
		}
	}

	/***
	 * Negate the cobody.
	 * @return A body of the negation of the this.
	 */
	public HornClauseBody negate() {
		assert !mFinalized;
		final HornClauseBody res = new HornClauseBody(mParserScript);
		res.mergeCobody(this);
		return res;
	}

	/***
	 * Get the transition formula of the cobody.
	 * @param script
	 * @return
	 */
	public Term getTransitionFormula(final Script parserScript) {
		final Term[] transitions = mTransitions.toArray(new Term[mTransitions.size()]);
//		return theory.and(transitions);
		return SmtUtils.and(parserScript, transitions);
	}

	List<HornClausePredicateSymbol> getPredicates(final HCSymbolTable symbolTable) {
		computePredicates(symbolTable);

		return mPredicateSymbols;
	}

	/***
	 * Get a map from literals to TermVariable.
	 * @param symbolTable
	 * @return
	 */
	public List<List<TermVariable>> getPredicateToVars(final HCSymbolTable symbolTable) {
		computePredicates(symbolTable);
		return mPredicateSymbolToVariables;

//		final List<List<TermVariable>> res = new ArrayList<>();
//		for (final ApplicationTerm predicate : mPredicates) {
//			final ArrayList<TermVariable> vars = new ArrayList<>();
//			for (final Term par : predicate.getParameters()) {
//				vars.add((TermVariable) par);
//			}
//
//			res.put(symbolTable.getOrConstructHornClausePredicateSymbol(
//						predicate.getFunction().getName(), predicate.getFunction().getParameterSorts()),
//					vars);
//		}
//		return res;
	}

	private void computePredicates(final HCSymbolTable symbolTable) {
		if (mFinalized) {
			// already did this before
			return;
		}

		for (final ApplicationTerm pred : mPredicates) {
			final HornClausePredicateSymbol bodySymbol = symbolTable.getOrConstructHornClausePredicateSymbol(
					pred.getFunction().getName(), pred.getFunction().getParameterSorts());
			mPredicateSymbols.add(bodySymbol);
			for (final Term par : pred.getParameters()) {
				assert par instanceof TermVariable;
			}
			final List<TermVariable> parameterTermVariables = Arrays.asList(pred.getParameters()).stream()
					.map(t -> (TermVariable) t)
					.collect(Collectors.toList());
//			assert parameterTermVariables.size() == new HashSet<>(parameterTermVariables).size() : "TODO: eliminate "
//					+ "duplicate arguments";
			final List<TermVariable> bodyVars = parameterTermVariables;
			mPredicateSymbolToVariables.add(bodyVars);
		}
		mFinalized = true;
	}

	@Override
	public String toString() {
		final StringBuilder result = new StringBuilder("");

		boolean first = true;
		for (final ApplicationTerm t : mPredicates) {
			if (!first) {
				result.append(" && ");

			}
			result.append(t.toString());
			first = false;
		}
		for (final Term t : mTransitions) {
			if (!first) {
				result.append(" && ");
			}
			result.append(t.toStringDirect());
			first = false;
		}
		return '(' + result.toString() + ')';
	}

	public void addToTransitionFormula(final Term binaryEquality) {
		// TODO Auto-generated method stub

	}
}
