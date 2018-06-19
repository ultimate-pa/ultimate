package de.uni_freiburg.informatik.ultimate.lib.chc;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Stores a set of constrained Horn clauses and provides various meta information about. Like:
 * <ul>
 *  <li> all Horn clauses with some given head predicate symbol
 *  <li> all head or body vars of reachable Horn clauses
 *  <li>
 * </ul>
 *
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class ChcPreMetaInfoProvider {

	private final HcSymbolTable mSymbolTable;
	private final List<HornClause> mHornClausesRaw;
	private final HashRelation<HcPredicateSymbol, HornClause> mHornClausesSorted;

	private final Set<HcPredicateSymbol> mAllReachablePredSymbols;

	// auxiliary variables
	private final Set<HcHeadVar> mAllHeadHcVars;
	private final Set<HcBodyVar> mAllBodyHcVars;

	// output variables
	private final List<HcHeadVar> mAllHeadHcVarsAsList;
	private final List<HcBodyVar> mAllBodyHcVarsAsList;

	public ChcPreMetaInfoProvider(final List<HornClause> hornClausesRaw, final HcSymbolTable symbolTable) {
		mHornClausesRaw = hornClausesRaw;
		mSymbolTable = symbolTable;
		mHornClausesSorted = sortHornClausesByHeads(hornClausesRaw);

		mAllReachablePredSymbols = new LinkedHashSet<>();

		mAllHeadHcVars = new LinkedHashSet<>();
		mAllBodyHcVars = new LinkedHashSet<>();
		mAllHeadHcVarsAsList = new ArrayList<>();
		mAllBodyHcVarsAsList = new ArrayList<>();

		compute();
	}

	private void compute() {

		final Deque<HcPredicateSymbol> headPredQueue = new ArrayDeque<>();
		final Set<HcPredicateSymbol> addedToQueueBefore = new HashSet<>();

		headPredQueue.push(mSymbolTable.getFalseHornClausePredicateSymbol());
		addedToQueueBefore.add(mSymbolTable.getFalseHornClausePredicateSymbol());

		while (!headPredQueue.isEmpty()) {
			// breadth-first (pollFirst) or depth-first (pop) should not matter here
			final HcPredicateSymbol headPredSymbol = headPredQueue.pop();

			mAllReachablePredSymbols.add(headPredSymbol);

			mAllHeadHcVars.addAll(mSymbolTable.getHcHeadVarsForPredSym(headPredSymbol, true));

			final Set<HornClause> hornClausesForHeadPred = mHornClausesSorted.getImage(headPredSymbol);

			for (final HornClause hornClause : hornClausesForHeadPred) {
				mAllBodyHcVars.addAll(hornClause.getBodyVariables());

				for (final HcPredicateSymbol bodyPredSym : hornClause.getBodyPredicates()) {
					if (!addedToQueueBefore.contains(bodyPredSym)) {
						headPredQueue.push(bodyPredSym);
						addedToQueueBefore.add(bodyPredSym);
					}
				}
			}
		}

		mAllHeadHcVarsAsList.addAll(mAllHeadHcVars);
		mAllBodyHcVarsAsList.addAll(mAllBodyHcVars);
	}

	private HashRelation<HcPredicateSymbol, HornClause> sortHornClausesByHeads(
			final List<HornClause> hornClausesRaw) {
		final HashRelation<HcPredicateSymbol, HornClause> hornClauseHeadPredicateToHornClauses =
				new HashRelation<>();

		for (final HornClause hc : hornClausesRaw) {
			if (hc.isHeadFalse()) {
				hornClauseHeadPredicateToHornClauses.addPair(mSymbolTable.getFalseHornClausePredicateSymbol(), hc);
			} else {
				hornClauseHeadPredicateToHornClauses.addPair(hc.getHeadPredicate(), hc);
			}
		}
		return hornClauseHeadPredicateToHornClauses;
	}

	public HashRelation<HcPredicateSymbol, HornClause> getHornClausesSorted() {
		return mHornClausesSorted;
	}

	public List<HcHeadVar> getAllHeadHcVarsAsList() {
		return Collections.unmodifiableList(mAllHeadHcVarsAsList);
	}

	public List<HcBodyVar> getAllBodyHcVarsAsList() {
		return Collections.unmodifiableList(mAllBodyHcVarsAsList);
	}

	public Set<HcPredicateSymbol> getAllReachablePredSymbols() {
		return mAllReachablePredSymbols;
	}
}