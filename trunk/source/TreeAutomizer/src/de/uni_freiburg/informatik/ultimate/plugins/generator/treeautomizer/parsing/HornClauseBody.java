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
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClause;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClausePredicateSymbol;
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

	/***
	 * Construct a Body of a Horn statement.
	 */
	public HornClauseBody() {
		mCobody = new HornClauseCobody();
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
	 * @param script
	 * @param symbolTable
	 * @return
	 */
	public HornClause convertToHornClause(final ManagedScript script, final HCSymbolTable symbolTable, final Theory theory) {
//		assert tt.size() <= 1;
//		final Map<HornClausePredicateSymbol, List<TermVariable>> tt = getBodyPredicateToVars(symbolTable);
//		final HornClausePredicateSymbol bodySymbol = tt.keySet().iterator().hasNext() ? tt.keySet().iterator().next()
//				: symbolTable.getFalseHornClausePredicateSymbol();
		
		/*
		 * Collect the predicate symbol and the arguments of the body predicate from the Term mHead
		 *  right now we assume that 
		 *   - all parameters of the head predicate are variables
		 *   - all parameters of the head predicate are pairwise different (i.e. there are no repeated variables)
		 *   TODO: lift this assumption by introducing equalities
		 */
		final HornClausePredicateSymbol bodySymbol; 
		final List<TermVariable> bodyVars;
		if (mHead != null) {
			bodySymbol = symbolTable.getOrConstructHornClausePredicateSymbol(
				mHead.getFunction().getName(), mHead.getFunction().getParameterSorts());
			final List<TermVariable> parameterTermVariables = Arrays.asList(mHead.getParameters()).stream()
					.map(t -> (TermVariable) t)
					.collect(Collectors.toList());
			assert parameterTermVariables.size() == new HashSet<>(parameterTermVariables).size() : "TODO: eliminate "
					+ "duplicate arguments";
			bodyVars = parameterTermVariables;
		} else {
			// if there is no explicit head symbol, then it is implicitly false (the neutral element wrt. disjunction)
			bodySymbol = symbolTable.getFalseHornClausePredicateSymbol();
			bodyVars = Collections.emptyList();
		}




		List<HornClausePredicateSymbol> cobodySymbols = mCobody.getPredicates(symbolTable);
		List<List<TermVariable>> cobobodyVars = mCobody.getPredicateToVars(symbolTable);
		
		return new HornClause(script, symbolTable,
				getTransitionFormula(script, theory),
				bodySymbol,
				bodyVars,
				cobodySymbols,
				cobobodyVars);
	}

	/***
	 * Set the head literal of the body.
	 * @param literal
	 * @return
	 */
	public boolean setHead(final ApplicationTerm literal) {
		if (mHead == null) {
			mHead = literal;
			return true;
		} else {
			return false;
		}
	}

	/***
	 * Merge the cobody of the body with the given cobody.
	 * @param cobody
	 */
	public void mergeCobody(final HornClauseCobody cobody) {
		this.mCobody.mergeCobody(cobody);
	}

	/***
	 * Add the transition formula to the cobody.
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
	public Term getTransitionFormula(ManagedScript script, Theory theory) {
		return mCobody.getTransitionFormula(script, theory);
	}
}
