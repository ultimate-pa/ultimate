/*
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */

package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.SortSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAnnotation.RuleKind;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ScopedArrayList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * Solver for the data type theory.
 *
 * This theory understands relations between data types, their constructors and selectors.
 * It propagates new equalities between data type terms as well as the arguments of their constructors.
 * It also detects all conflicts in these relations. It uses the equality graph of the CClosure class.
 *
 * @author Moritz Mohr
 *
 */
public class DataTypeTheory implements ITheory {

	private final Clausifier mClausifier;
	private final CClosure mCClosure;
	private final Theory mTheory;
	/**
	 * The list of cc-term pairs, whose equality we need to prpagate
	 */
	private final ArrayDeque<CCEquality> mPendingEqualities = new ArrayDeque<>();

	/**
	 * A pending datatype lemma. These will be processed at each setLiteral or at
	 * check points.
	 */
	private final ArrayDeque<DataTypeLemma> mPendingLemmas = new ArrayDeque<>();

	/**
	 * A map from selector name to the matching constructor. This is used as a cache
	 * for {@link #getConstructor(ApplicationTerm)}
	 */
	private final LinkedHashMap<String, Constructor> mSelectorMap = new LinkedHashMap<>();
	/**
	 * Collect all created terms to check after a backtrack if their equalities are still valid.
	 */
	private final ScopedArrayList<CCAppTerm> mRecheckOnBacktrack = new ScopedArrayList<>();
	/**
	 * This a cache for {@link #isInfinite(Sort, LinkedHashSet)}
	 */
	private final LinkedHashMap<Sort, Boolean> mInfinityMap = new LinkedHashMap<>();
	/**
	 * This maps from a pair of equal terms to a list of pairs of equal terms.
	 * The equalities of the term pairs in the list are the reason for the equality of the key pair
	 * and are used to generate the unit clause.
	 */
	private final LinkedHashMap<CCEquality, DataTypeLemma> mEqualityReasons = new LinkedHashMap<>();

	public DataTypeTheory(final Clausifier clausifier, final Theory theory, final CClosure cclosure) {
		mClausifier = clausifier;
		mCClosure = cclosure;
		mTheory = theory;
	}

	public void addPendingLemma(final DataTypeLemma lemma) {
		mPendingLemmas.add(lemma);
	}

	/**
	 * Process pending datatype lemmas. This adds the propagated literals to the
	 * pending equality queue or returns a conflict.
	 *
	 * @return a conflict clause if one was found, or null if not.
	 */
	private Clause processPendingLemmas() {
		for (final DataTypeLemma lemma : mPendingLemmas) {
			final SymmetricPair<CCTerm> eq = lemma.getMainEquality();
			if (eq == null) {
				// this is a conflict lemma, not a lemma that proves an equality.
				return computeClause(null, lemma);
			}
			if (eq.getFirst().mRepStar != eq.getSecond().mRepStar) {
				final CCEquality eqAtom = mCClosure.createEquality(eq.getFirst(), eq.getSecond(), false);
				if (eqAtom == null) {
					// this is a trivial disequality, so we need to create a conflict.
					return computeClause(null, lemma);
				} else if (eqAtom.getDecideStatus() == eqAtom.negate()) {
					// this is a conflict, as the propagated equality is already set negatively
					return computeClause(eqAtom, lemma);
				} else {
					// add the lemma to pending equalities
					mPendingEqualities.add(eqAtom);
					mEqualityReasons.put(eqAtom, lemma);
				}
			}
		}
		mPendingLemmas.clear();
		return null;
	}

	@Override
	public Clause startCheck() {
		return null;
	}

	@Override
	public void endCheck() {
	}

	@Override
	public Clause setLiteral(final Literal literal) {
		if (literal instanceof CCEquality) {
			final CCEquality cceq = (CCEquality) literal;

			computeInjectiveDisjointLemmas(cceq.getLhs(), cceq.getRhs());
		}
		return processPendingLemmas();
	}

	/**
	 * Check if lhs and rhs are constructor applications and compute corresponding
	 * disjoint and injectivity lemmas. This is called when lhs and rhs are equal.
	 * If they are different constructors applications, a disjoint conflict should
	 * be created, stating that lhs and rhs cannot be equal. If they are the same
	 * constructor, an injectivity lemma is created for each argument to ensure that
	 * the arguments are equal.
	 *
	 * The lemmas are added to pending lemmas and should be processed afterwards.
	 *
	 * @param lhs The first CCTerm.
	 * @param rhs The second CCTerm.
	 */
	private void computeInjectiveDisjointLemmas(CCTerm lhs, CCTerm rhs) {
		if (isConstructorApp(lhs.mFlatTerm) && isConstructorApp(rhs.mFlatTerm)) {
			final ApplicationTerm lhsApp = (ApplicationTerm) lhs.getFlatTerm();
			final ApplicationTerm rhsApp = (ApplicationTerm) rhs.getFlatTerm();
			@SuppressWarnings("unchecked")
			final SymmetricPair<CCTerm>[] reason = new SymmetricPair[] { new SymmetricPair<>(lhs, rhs) };
			if (lhsApp.getFunction() == rhsApp.getFunction()) {
				for (int i = 0; i < lhsApp.getParameters().length; i++) {
					final CCTerm lhsArg = mClausifier.getCCTerm(lhsApp.getParameters()[i]);
					final CCTerm rhsArg = mClausifier.getCCTerm(rhsApp.getParameters()[i]);
					if (rhsArg.mRepStar != lhsArg.mRepStar) {
						final SymmetricPair<CCTerm> eqPair = new SymmetricPair<>(lhsArg, rhsArg);
						// dt_injective: cons(args1) != cons(args2) or args1[i] == args2[i]
						addPendingLemma(new DataTypeLemma(RuleKind.DT_INJECTIVE, eqPair, reason, lhs, rhs));
					}
				}
			} else {
				// dt_disjoint: cons1(args1) != cons2(args2)
				addPendingLemma(new DataTypeLemma(RuleKind.DT_DISJOINT, reason, lhs, rhs));
			}
		}

	}

	@Override
	public void backtrackLiteral(final Literal literal) {
	}

	@Override
	public Clause checkpoint() {
		final Clause conflict = processPendingLemmas();
		if (conflict != null) {
			return conflict;
		}

		// Visit all ((_ is CONS) u) terms that are true and try to apply rule 3 or 9 on
		// them
		final CCTerm trueCC = mClausifier.getCCTerm(mTheory.mTrue);
		final LinkedHashMap<CCTerm, CCAppTerm> visited = new LinkedHashMap<>();
		for (final CCTerm t : trueCC.getRepresentative().mMembers) {
			if (t instanceof CCAppTerm && t.mFlatTerm instanceof ApplicationTerm) {
				final ApplicationTerm at = (ApplicationTerm) t.mFlatTerm;
				final CCAppTerm trueIsApp = (CCAppTerm) t;
				if (at.getFunction().getName() == "is") {
					final CCTerm argRep = trueIsApp.getArg().getRepresentative();
					if (!visited.containsKey(argRep)) {
						visited.put(argRep, trueIsApp);
						addConstructorLemma(trueIsApp);
					} else {
						/*
						 * Rule 9:
						 * Since a constructor can't be equal to another constructor,
						 * there must not be multiple true is functions that test for different constructors.
						 */
						final CCAppTerm prevIsApp = visited.get(argRep);
						if (prevIsApp.getFunc() != trueIsApp.getFunc()) {
							final ArrayList<SymmetricPair<CCTerm>> reason = new ArrayList<>();
							reason.add(new SymmetricPair<>(prevIsApp, trueCC));
							reason.add(new SymmetricPair<>(trueIsApp, trueCC));
							if (prevIsApp.getArg() != trueIsApp.getArg()) {
								reason.add(new SymmetricPair<>(prevIsApp.getArg(), trueIsApp.getArg()));
							}
							final Term[] testers = new Term[2];
							testers[0] = prevIsApp.mFlatTerm;
							testers[1] = trueIsApp.mFlatTerm;
							@SuppressWarnings("unchecked")
							final DataTypeLemma lemma = new DataTypeLemma(RuleKind.DT_UNIQUE,
									reason.toArray(new SymmetricPair[reason.size()]), testers);
							mClausifier.getLogger().debug("Conflict: Rule 9");
							return computeClause(null, lemma);
						}
					}
				}
			}
		}

		// collect all cc-terms that have a "is" function as parent which is equal to false
		final LinkedHashMap<CCTerm, LinkedHashSet<CCTerm>> falseIsFuns = new LinkedHashMap<>();
		final CCTerm falseCC = mClausifier.getCCTerm(mTheory.mFalse);
		for (final CCTerm cct : falseCC.getRepresentative().mMembers) {
			if (cct.mFlatTerm instanceof ApplicationTerm && ((ApplicationTerm) cct.mFlatTerm).getFunction().getName().equals("is")) {
				falseIsFuns.putIfAbsent(((CCAppTerm)cct).mArg.mRepStar, new LinkedHashSet<>());
				falseIsFuns.get(((CCAppTerm)cct).mArg.mRepStar).add(cct);
			}
		}

		for (final CCTerm cct : falseIsFuns.keySet()) {
			final DataType dt = (DataType) cct.mFlatTerm.getSort().getSortSymbol();
			if (falseIsFuns.get(cct).size() >= dt.getConstructors().length) {
				final LinkedHashMap<String, CCTerm> isIndices = new LinkedHashMap<>();
				for (final CCTerm isFun : falseIsFuns.get(cct)) {
					isIndices.put(((ApplicationTerm) isFun.mFlatTerm).getFunction().getIndices()[0], isFun);
				}
				/*
				 * Rule 6:
				 * Every data type term must be equal to a constructor.
				 * Thus, not all "is" functions may be false.
				 */
				if (isIndices.size() == dt.getConstructors().length) {
					final ArrayList<SymmetricPair<CCTerm>> reason = new ArrayList<>();
					final Term[] testers = new Term[dt.getConstructors().length];
					int i = 0;
					CCTerm firstArg = null;
					for (final Constructor consName : dt.getConstructors()) {
						final CCTerm isFun = isIndices.get(consName.getName());
						testers[i++] = isFun.mFlatTerm;
						final CCTerm arg = ((CCAppTerm)isFun).mArg;
						reason.add(new SymmetricPair<>(isFun, falseCC));
						if (firstArg == null) {
							firstArg = arg;
						} else if (firstArg != arg) {
							reason.add(new SymmetricPair<>(firstArg, arg));
						}
					}
					@SuppressWarnings("unchecked")
					final DataTypeLemma lemma = new DataTypeLemma(RuleKind.DT_CASES,
							reason.toArray(new SymmetricPair[reason.size()]), testers);
					mClausifier.getLogger().debug("Conflict: Rule 6");
					return computeClause(null, lemma);
				}
			}
		}

		return processPendingLemmas();
	}

	private Clause checkDTCycles() {
		// check for cycles (Rule7)
		/*
		 * Rule 7:
		 * Constructor arguments must not contain the constructor term itself, so we need to check
		 * if there is any cycle in the equality graph.
		 * To do this, we do a depth-first-search over the graph, noting terms (visitedOnPath) already visited
		 * to detect a cycle.
		 */

		// Remember the representatives of all visited terms in this set to avoid
		// searching the same sub tree more than once.
		final Set<CCTerm> visited = new HashSet<>();

		// Remember the current path.
		final Deque<CCTerm> path = new ArrayDeque<>();
		// Remember the representatives of all nodes on the current path.
		final Set<CCTerm> visitedOnPath = new HashSet<>();
		final Deque<CCTerm> todo = new ArrayDeque<>();
		final Map<CCTerm, CCAppTerm> trueTesters = new HashMap<>();

		for (final CCTerm start : mCClosure.mAllTerms) {
			if (start.mFlatTerm != null && start.mFlatTerm.getSort().getSortSymbol().isDatatype()) {
				todo.push(start);

				while (!todo.isEmpty()) {
					final CCTerm ct = todo.pop();
					final CCTerm rep = ct.getRepresentative();

					if (visited.contains(rep)) {
						if (path.peek() == ct) {
							path.pop();
							visitedOnPath.remove(rep);
						} else {
							assert !visitedOnPath.contains(rep);
						}
						continue;
					}

					final List<CCTerm> children = getAllDataTypeChildren(rep, trueTesters);

					if (!children.isEmpty()) {
						path.push(ct);
						visitedOnPath.add(rep);
						todo.push(ct);

						for (final CCTerm c : children) {
							if (visitedOnPath.contains(c.getRepresentative())) {
								// one of the children is already on the path so we found a cycle
								return buildCycleConflict(c, path, trueTesters);
							}
							todo.push(c);
						}
					}
					visited.add(rep);
				}
			}
		}
		return null;
	}

	@Override
	public Clause computeConflictClause() {

		// Get list of all data types. This prevents a concurrent modification error.
		final List<CCTerm> dataTypeTerms = new ArrayList<>();
		for (final CCTerm ct : mCClosure.mAllTerms) {
			if (ct == ct.mRep && ct.mFlatTerm != null && ct.mFlatTerm.getSort().getSortSymbol().isDatatype()) {
				dataTypeTerms.add(ct);
			}
		}
		for (final CCTerm ct : dataTypeTerms) {
			createIsApplications(ct);
		}

		final Clause conflict = checkDTCycles();
		if (conflict != null) {
			return conflict;
		}

		if (!mPendingLemmas.isEmpty()) {
			return processPendingLemmas();
		}

		// paranoid checks to see if all select-over-cons and test-over-cons terms were detected by
		// reverse trigger.
		// first we collect one cons-terms for each congruence class:
		for (final CCTerm rep : mCClosure.mAllTerms) {
			if (rep.getRepresentative() != rep) {
				continue;
			}
			for (final CCTerm member : rep.mMembers) {
				if (isConstructorApp(member.mFlatTerm)) {
					final ApplicationTerm memberAt = (ApplicationTerm) member.mFlatTerm;
					assert rep.getSharedTerm() != null;
					if (member != rep.getSharedTerm()) {
						final CCTerm consTerm = rep.getSharedTerm();
						final ApplicationTerm consAt = (ApplicationTerm) consTerm.mFlatTerm;
						if (((ApplicationTerm)member.mFlatTerm).getFunction()
								!= ((ApplicationTerm)consTerm.mFlatTerm).getFunction()) {
							mCClosure.getLogger().error("Unpropagated equality on different conses");
							computeInjectiveDisjointLemmas(consTerm, member);
						} else {
							// check we propagated all equalities between constructor arguments.
							for (int i = 0; i < memberAt.getParameters().length; i++) {
								final CCTerm consArg = mClausifier.getCCTerm(consAt.getParameters()[i]);
								final CCTerm memArg = mClausifier.getCCTerm(memberAt.getParameters()[i]);
								if (memArg.mRepStar != consArg.mRepStar) {
									mCClosure.getLogger().error("Unpropagated constructor argument equality");
									computeInjectiveDisjointLemmas(consTerm, member);
								}
							}
						}
					}
				}
			}
		}
		for (final CCTerm ccTerm : mCClosure.mAllTerms) {
			if (!(ccTerm.getFlatTerm() instanceof ApplicationTerm)) {
				continue;
			}
			final ApplicationTerm appTerm = (ApplicationTerm) ccTerm.getFlatTerm();
			final FunctionSymbol fs = appTerm.getFunction();
			if (appTerm.getFunction().isSelector() || appTerm.getFunction().getName().equals("is")) {
				final CCTerm argTerm = ((CCAppTerm) ccTerm).getArg();
				final CCTerm consTerm = argTerm.getRepresentative().getSharedTerm();
				if (consTerm != null) {
					final ApplicationTerm consApp = (ApplicationTerm) consTerm.getFlatTerm();
					final DataType datatype = (DataType) consApp.getSort().getSortSymbol();
					final Constructor constructor = datatype.getConstructor(consApp.getFunction().getName());
					if (appTerm.getFunction().getName().equals("is")) {
						final Term truthValue;
						if (fs.getIndices()[0].equals(constructor.getName())) {
							truthValue = mClausifier.getTheory().mTrue;
						} else {
							truthValue = mClausifier.getTheory().mFalse;
						}
						final CCTerm truthCC = mClausifier.getCCTerm(truthValue);
						if (ccTerm.getRepresentative() != truthCC.getRepresentative()) {
							mCClosure.getLogger().error("Unpropagated is of constructor");
							@SuppressWarnings("unchecked")
							final SymmetricPair<CCTerm>[] reason = new SymmetricPair[] { new SymmetricPair<>(consTerm, argTerm) };
							final SymmetricPair<CCTerm> mainEq = new SymmetricPair<>(ccTerm, truthCC);
							final DataTypeLemma lemma = new DataTypeLemma(RuleKind.DT_TESTER, mainEq, reason, consTerm);
							addPendingLemma(lemma);
						}
					} else if (appTerm.getFunction().isSelector()) {
						final String[] allSelectorNames = constructor.getSelectors();
						for (int i = 0; i < allSelectorNames.length; i++) {
							if (allSelectorNames[i].equals(appTerm.getFunction().getName())) {
								final CCTerm consArg = mClausifier.getCCTerm(consApp.getParameters()[i]);
								if (ccTerm.getRepresentative() != consArg.getRepresentative()) {
									mCClosure.getLogger().error("Unpropagated selector of constructor");
									@SuppressWarnings("unchecked")
									final SymmetricPair<CCTerm>[] reason = new SymmetricPair[] {
											new SymmetricPair<>(consTerm, argTerm) };
									final SymmetricPair<CCTerm> mainEq = new SymmetricPair<>(ccTerm, consArg);
									final DataTypeLemma lemma = new DataTypeLemma(RuleKind.DT_PROJECT, mainEq, reason,
											consTerm);
									addPendingLemma(lemma);
								}
							}
						}
					}
				}
			}
		}
		return processPendingLemmas();
	}

	/**
	 * Return all select or is applications for a given ccTerm and return them as a
	 * map. This takes the congruence class into account and returns all function
	 * applications of any member of the class, but at most one per function symbol.
	 *
	 * @param ccTerm The term whose applications should be searched. Must be the
	 *               representative of its class.
	 */
	private Map<FunctionSymbol, CCAppTerm> getSelectorsAndTesters(final CCTerm ccTerm) {
		assert ccTerm == ccTerm.getRepresentative();
		final LinkedHashMap<FunctionSymbol, CCAppTerm> map = new LinkedHashMap<>();
		CCParentInfo pInfo = ccTerm.mCCPars;
		while (pInfo != null) {
			if (pInfo.mCCParents != null && !pInfo.mCCParents.isEmpty()) {
				// only the first parent needs to be checked, as each select/is call is
				// congruent.
				final CCAppTerm p = pInfo.mCCParents.iterator().next().getData();
				if (p.mFlatTerm instanceof ApplicationTerm) {
					final FunctionSymbol pFun = ((ApplicationTerm) p.mFlatTerm).getFunction();
					if (pFun.isSelector() || pFun.getName().equals(SMTLIBConstants.IS)) {
						map.put(pFun, p);
					}
				}
			}
			pInfo = pInfo.mNext;
		}
		return map;
	}

	/**
	 * This functions searches all data type children of a given term. This means,
	 * if there is a constructor term, that it is equal to the given term, it finds
	 * all of its argument with a data type sort. If there is no such constructor
	 * term, it searches for applications of selector term on the equality class and
	 * returns all selector term, which could be valid applications.
	 *
	 * @param ccTerm   The representative of the equality class.
	 * @param children An empty list, which will be filled with children if there
	 *                 are any.
	 * @return The constructor term which is equal to rep, if there is none, it
	 *         returns a true "is" function for this equality class, if there is
	 *         also none, it returns null.
	 */
	private List<CCTerm> getAllDataTypeChildren(final CCTerm ccTerm, final Map<CCTerm, CCAppTerm> trueTesters) {
		final ArrayList<CCTerm> children = new ArrayList<>();
		final CCTerm rep = ccTerm.getRepresentative();
		/*
		 * first check if there is a cons in the equivalence class. If yes, add all
		 * arguments to children and return the cons.
		 */
		final CCTerm sharedTerm = rep.getSharedTerm();
		if (sharedTerm != null) {
			CCTerm func = sharedTerm;
			while (func instanceof CCAppTerm) {
				final CCAppTerm appTerm = (CCAppTerm) func;
				final CCTerm arg = appTerm.getArg();
				if (arg.getFlatTerm().getSort().getSortSymbol().isDatatype()) {
					children.add(arg);
				}
				func = appTerm.getFunc();
			}
			return children;
		}

		final DataType datatype = (DataType) rep.mFlatTerm.getSort().getSortSymbol();
		final CCTerm trueRep = mClausifier.getCCTerm(mTheory.mTrue).mRepStar;
		final Set<CCAppTerm> selectors = new LinkedHashSet<>();
		FunctionSymbol trueTester = null;
		final Set<FunctionSymbol> falseTesters = new LinkedHashSet<>();
		for (final Map.Entry<FunctionSymbol, CCAppTerm> entry : getSelectorsAndTesters(rep).entrySet()) {
			final FunctionSymbol func = entry.getKey();
			if (func.isSelector()) {
				if (func.getReturnSort().getSortSymbol().isDatatype()) {
					selectors.add(entry.getValue());
				}
			} else {
				// func is a tester
				final CCAppTerm tester = entry.getValue();
				if (tester.getRepresentative() == trueRep) {
					assert trueTester == null;
					trueTester = func;
					trueTesters.put(rep, tester);
				} else {
					falseTesters.add(func);
				}
			}
		}

		if (trueTester != null) {
			/* we know which constructor created the term, so return only matching selectors */
			final Constructor c = datatype.getConstructor(trueTester.getIndices()[0]);
			final Set<String> validSelectors = new HashSet<>();
			validSelectors.addAll(Arrays.asList(c.getSelectors()));

			for (final CCAppTerm s : selectors) {
				if (validSelectors.contains(((ApplicationTerm)s.mFlatTerm).getFunction().getName())) {
					children.add(s);
				}
			}
		} else {
			/* we know at least which selectors cannot be right */
			final Set<String> invalidSelectors = new HashSet<>();
			for (final FunctionSymbol falseTester : falseTesters) {
				final Constructor c = datatype.getConstructor(falseTester.getIndices()[0]);
				invalidSelectors.addAll(Arrays.asList(c.getSelectors()));
			}
			for (final CCAppTerm s : selectors) {
				if (!invalidSelectors.contains(((ApplicationTerm) s.mFlatTerm).getFunction().getName())) {
					children.add(s);
				}
			}
		}
		return children;
	}

	/**
	 * This function builds the conflict clause for a path that contains a cycle.
	 * If there is one equality class on the path for which it is not sure whether it is the constructor in question,
	 * it builds an "is" term to let the dpll engine decide.
	 *
	 * @param currentTerm The term whose equality class already appeared on the path.
	 * @param path The list of representatives of equality classes in order of visit.
	 * @param argConsPairs A table of representatives of equality classes
	 *  which point to the argument of the preceding constructor and the constructor which argument is next in the path.
	 * @param possibleCons A collection of representatives of equality classes that have no constructor function as member, but could have.
	 * @return a conflict clause for the cyclic part of path, if there is for all equality classes in path a constructor term in the equality class or a true "is" term of the equality class.
	 * If for one equality class there is no constructor or "is" term, it returns null.
	 */
	private Clause buildCycleConflict(final CCTerm currentTerm, final Deque<CCTerm> path,
			final Map<CCTerm, CCAppTerm> trueTesters) {
		final ArrayList<SymmetricPair<CCTerm>> reason = new ArrayList<>();
		final ArrayDeque<CCTerm> cycle = new ArrayDeque<>();
		final CCTerm trueCC = mClausifier.getCCTerm(mTheory.mTrue);
		final CCTerm currentTermRep = currentTerm.mRepStar;
		CCTerm currentAsChild = currentTerm;
		cycle.addFirst(currentTerm);
		while (true) {
			final CCTerm prevAsChild = path.pop();
			CCTerm prevAsParent = prevAsChild.getRepresentative().getSharedTerm();
			// if it is not sure that pathRep is the matching constructor to the selector (lastCT)
			// build the corresponding is-function
			if (prevAsParent == null) {
				// there is no constructor for the previous step. So lastCt should be a
				// selector.
				// Get the corresponding tester or create it if it does not exists.
				// If it exists, the corresponding tester is true.
				prevAsParent = ((CCAppTerm) currentAsChild).getArg();
				final ApplicationTerm selectorApp = (ApplicationTerm) currentAsChild.getFlatTerm();
				final FunctionSymbol selectorFunc = selectorApp.getFunction();
				final Constructor cons = getConstructor(selectorFunc);
				final Term isTerm = mTheory.term(mTheory.getFunctionWithResult("is", new String[] { cons.getName() },
						null, selectorFunc.getParameterSorts()[0]), prevAsParent.getFlatTerm());
				final CCTerm trueTester = mClausifier.getCCTerm(isTerm);
				if (trueTester == null) {
					mClausifier.createCCTerm(isTerm, SourceAnnotation.EMPTY_SOURCE_ANNOT);
					return null;
				}
				assert trueTester.getRepresentative() == trueCC.getRepresentative();
				reason.add(new SymmetricPair<>(trueTester, trueCC));
			}

			cycle.addFirst(prevAsParent);
			assert prevAsChild.getRepresentative() == prevAsParent.getRepresentative();
			if (prevAsChild.getRepresentative() == currentTermRep) {
				// this is the end of the cycle.
				cycle.addFirst(currentTerm);
				if (currentTerm != prevAsParent) {
					reason.add(new SymmetricPair<>(currentTerm, prevAsParent));
				}
				break;
			}

			cycle.addFirst(prevAsChild);
			if (prevAsChild != prevAsParent) {
				reason.add(new SymmetricPair<>(prevAsChild, prevAsParent));
			}
			currentAsChild = prevAsChild;
		}
		@SuppressWarnings("unchecked")
		final DataTypeLemma lemma = new DataTypeLemma(RuleKind.DT_CYCLE,
				reason.toArray(new SymmetricPair[reason.size()]), cycle.toArray(new CCTerm[cycle.size()]));
		mClausifier.getLogger().debug("Found Cycle: %s", cycle);
		return computeClause(null, lemma);
	}

	public Clause computeClause(final CCEquality eq, final DataTypeLemma lemma) {
		final boolean isProofEnabled = mClausifier.getEngine().isProofGenerationEnabled();
		final CongruencePath cp = new CongruencePath(mCClosure);
		return cp.computeDTLemma(eq, lemma, isProofEnabled);
	}

	@Override
	public Literal getPropagatedLiteral() {
		if (!mPendingEqualities.isEmpty()) {
			return mPendingEqualities.poll();
		}
		return null;
	}

	@Override
	public Clause getUnitClause(final Literal literal) {
		final CCEquality eq = (CCEquality) literal;

		return computeClause(eq, mEqualityReasons.get(eq));
	}

	@Override
	public Literal getSuggestion() {
		return null;
	}

	@Override
	public int checkCompleteness() {
		return 0;
	}

	@Override
	public void printStatistics(final LogProxy logger) {
	}

	@Override
	public void dumpModel(final LogProxy logger) {
	}

	@Override
	public void increasedDecideLevel(final int currentDecideLevel) {
	}

	@Override
	public void decreasedDecideLevel(final int currentDecideLevel) {
	}

	public void addRecheckOnBacktrack(final CCAppTerm newAppTerm) {
		mRecheckOnBacktrack.add(newAppTerm);
	}

	@Override
	public void backtrackStart() {
		mPendingLemmas.clear();
		mPendingEqualities.clear();
	}

	@SuppressWarnings("unchecked")
	public void recheckTrigger() {
		final Iterator<CCAppTerm> iter = mRecheckOnBacktrack.iterator();
		while (iter.hasNext()) {
			CCTerm constructorCCTerm = null;
			ApplicationTerm constructor = null;
			final CCAppTerm checkTerm = iter.next();
			final ApplicationTerm selectOrIsTerm = (ApplicationTerm) checkTerm.mFlatTerm;
			final FunctionSymbol selectorOrTester = selectOrIsTerm.getFunction();
			final CCTerm selectOrIsArg = checkTerm.getArg();
			assert selectorOrTester.isSelector() || selectorOrTester.getName().equals(SMTLIBConstants.IS);
			for (final CCTerm ct : selectOrIsArg.getRepresentative().mMembers) {
				if (ct.mFlatTerm instanceof ApplicationTerm && ((ApplicationTerm) ct.mFlatTerm).getFunction().isConstructor()) {
					constructorCCTerm = ct;
					constructor = (ApplicationTerm) ct.mFlatTerm;
					break;
				}
			}
			if (constructor == null) {
				iter.remove();
				continue;
			}
			SymmetricPair<CCTerm>[] reason;
			if (selectOrIsArg != constructorCCTerm) {
				reason = new SymmetricPair[] { new SymmetricPair<>(selectOrIsArg, constructorCCTerm) };
			} else {
				reason = new SymmetricPair[0];
			}
			if (selectorOrTester.isSelector()) {
				final String selName = selectorOrTester.getName();
				final Constructor c = getConstructor(selectorOrTester);
				assert c.getName().equals(constructor.getFunction().getName());
				for (int i = 0; i < c.getSelectors().length; i++) {
					if (selName.equals(c.getSelectors()[i])) {
						final CCTerm arg = mClausifier.getCCTerm(constructor.getParameters()[i]);
						if (arg.mRepStar != checkTerm.mRepStar) {
							final SymmetricPair<CCTerm> provedEq = new SymmetricPair<>(checkTerm, arg);
							final DataTypeLemma lemma = new DataTypeLemma(RuleKind.DT_PROJECT, provedEq, reason,
									constructorCCTerm);
							addPendingLemma(lemma);
						}
					}
				}
			} else {
				assert constructor.getFunction().getName().equals(selectorOrTester.getIndices()[0]);
				final CCTerm ccTrue = mClausifier.getCCTerm(mTheory.mTrue);
				if (ccTrue.mRepStar != checkTerm.mRepStar) {
					final SymmetricPair<CCTerm> provedEq = new SymmetricPair<>(checkTerm,
							mClausifier.getCCTerm(mTheory.mTrue));
					final DataTypeLemma lemma = new DataTypeLemma(RuleKind.DT_TESTER, provedEq, reason,
							constructorCCTerm);
					addPendingLemma(lemma);
				}
			}
		}
	}

	@Override
	public Clause backtrackComplete() {
		// if we constructed new terms, their equalities have been removed in the backtracking process,
		// so we need to check if they are still valid.
		recheckTrigger();
		return processPendingLemmas();
	}

	@Override
	public void backtrackAll() {
	}

	@Override
	public void restart(final int iteration) {
	}

	@Override
	public void removeAtom(final DPLLAtom atom) {
	}

	@Override
	public void push() {
		mRecheckOnBacktrack.beginScope();
	}

	@Override
	public void pop() {
		mPendingLemmas.clear();
		mPendingEqualities.clear();
		mInfinityMap.clear();
		mRecheckOnBacktrack.endScope();
		recheckTrigger();
	}

	@Override
	public Object[] getStatistics() {
		return new Object[] { ":DT" };
	}

	/**
	 * Rule 3 checks if the argument of a true isTerm has an application for every
	 * selector function and if so, builds a constructor term based on these
	 * selector functions. It also builds the lemma stating that the constructor
	 * term equals the argument.
	 *
	 * @param isTerm a "is" function term equal to true.
	 */
	private void addConstructorLemma(final CCAppTerm isTerm) {
		// check if there is already a constructor application equal to the argument
		final CCTerm arg = isTerm.mArg;
		if (arg.getRepresentative().getSharedTerm() != null) {
			// We don't care which constructor it is. If it's the wrong constructor
			// there should already be a trigger that set the isTerm to false.
			return;
		}
		final ApplicationTerm at = (ApplicationTerm) isTerm.mFlatTerm;
		final String consName = at.getFunction().getIndices()[0];

		// check if there are all selector applications on the eq class
		final Term dtTerm = arg.mFlatTerm;
		final DataType dt = (DataType) dtTerm.getSort().getSortSymbol();
		final Constructor c = dt.getConstructor(consName);

		if (checkMissingInfiniteSelector(arg, c)) {
			// The constructor has a missing infinite selector.
			// We don't need to actually instantiate the lemma as we can always
			// create a fresh cons term.
			return;
		}
		final Term[] selectorTerms = new Term[c.getSelectors().length];
		for (int i = 0; i < selectorTerms.length; i++) {
			selectorTerms[i] = mTheory.term(c.getSelectors()[i], dtTerm);
		}
		// create a new constructor application like C(s1(x), s2(x), ..., sm(x))
		final Sort consType = c.needsReturnOverload() ? dtTerm.getSort() : null;
		final Term consTerm = mTheory.term(consName, null, consType, selectorTerms);
		final CCTerm consCCTerm = mClausifier.createCCTerm(consTerm, SourceAnnotation.EMPTY_SOURCE_ANNOT);
		final SymmetricPair<CCTerm> eq = new SymmetricPair<>(arg, consCCTerm);
		@SuppressWarnings("unchecked")
		final DataTypeLemma lemma = new DataTypeLemma(RuleKind.DT_CONSTRUCTOR, eq,
				new SymmetricPair[] { new SymmetricPair<>(isTerm, mClausifier.getCCTerm(mTheory.mTrue)) });
		mClausifier.getLogger().debug("New DT_CONSTRUCTOR lemma for %s", dtTerm);
		addPendingLemma(lemma);
	}

	private boolean checkMissingInfiniteSelector(final CCTerm ccterm, Constructor constr) {
		// check if only selectors with finite return sort are missing and build them
		final Sort dataTypeSort = ccterm.mFlatTerm.getSort();
		for (int i = 0; i < constr.getArgumentSorts().length; i++) {
			if (isInfinite(constr.getArgumentSorts()[i])) {
				final FunctionSymbol selector = mTheory.getFunction(constr.getSelectors()[i], dataTypeSort);
				if (mCClosure.getAllFuncAppsForArg(selector, ccterm, 0).isEmpty()) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Rule 5 constructs an "is" term if there is a function application for every selector
	 * of the tested constructor on the given term.
	 *
	 * @param ccterm
	 */
	private void createIsApplications(final CCTerm ccterm) {
		final SortSymbol sym = ccterm.mFlatTerm.getSort().getSortSymbol();

		// check if there is already a constructor.
		// in that case no "is" term is created.
		if (ccterm.getSharedTerm() != null) {
			return;
		}

		for (final Constructor c : ((DataType) sym).getConstructors()) {
			if (!checkMissingInfiniteSelector(ccterm, c)) {
				final FunctionSymbol isFs = mTheory.getFunctionWithResult("is", new String[] {c.getName()}, null, new Sort[] {ccterm.getFlatTerm().getSort()});
				final Term isTerm = mTheory.term(isFs, ccterm.mFlatTerm);
				if (mClausifier.getCCTerm(isTerm) == null) {
					mClausifier.createCCTerm(isTerm, SourceAnnotation.EMPTY_SOURCE_ANNOT);
				}
			}
		}
	}

	/**
	 * This function determines if a given sort is infinite or not.
	 *
	 * @param sort the sort in question.
	 * @return True if sort is infinite else False
	 */
	private boolean isInfinite(final Sort sort) {
		final Boolean cacheVal = mInfinityMap.get(sort);
		if (cacheVal != null) {
			return cacheVal;
		}
		final ArrayDeque<Sort> todo = new ArrayDeque<>();
		final Set<Sort> dependent = new LinkedHashSet<>();
		todo.push(sort);
		todo_loop: while (!todo.isEmpty()) {
			final Sort currSort = todo.pop();
			if (currSort.getSortSymbol().isDatatype() || currSort.isArraySort()) {
				final Set<Sort> subSorts = new LinkedHashSet<>();
				if (currSort.getSortSymbol().isDatatype()) {
					for (final Constructor c : ((DataType) currSort.getSortSymbol()).getConstructors()) {
						subSorts.addAll(Arrays.asList(c.getArgumentSorts()));
					}
				} else {
					subSorts.addAll(Arrays.asList(currSort.getArguments()));
				}
				final Iterator<Sort> iterator = subSorts.iterator();
				while (iterator.hasNext()) {
					final Sort argSort = iterator.next();
					final Boolean cv = mInfinityMap.get(argSort);
					if (cv != null) {
						iterator.remove();
						if (cv == true) {
							mInfinityMap.put(currSort, true);
							dependent.remove(currSort);
							continue todo_loop;
						}
					} else if (dependent.contains(argSort)) {
						mInfinityMap.put(currSort, true);
						dependent.remove(currSort);
						continue todo_loop;
					}
				}
				if (!subSorts.isEmpty()) {
					todo.push(currSort);
					dependent.add(currSort);
					for (final Sort s : subSorts) {
						todo.push(s);
					}
				} else {
					mInfinityMap.put(currSort, false);
					dependent.remove(currSort);
				}
			} else if (currSort.isNumericSort()) {
				mInfinityMap.put(currSort, true);
			} else {
				mInfinityMap.put(currSort, false);
			}
		}

		return mInfinityMap.get(sort);
	}

	/**
	 * Find the corresponding constructor to the given selector function.
	 *
	 * @param selector
	 * @return The constructor for which "selector" is a valid selector function.
	 */
	private Constructor getConstructor(final FunctionSymbol selector) {
		assert selector.isSelector() : "Not a selector";

		final String selName = selector.getName();
		final Constructor cons = mSelectorMap.get(selName);
		if (cons != null) {
			return cons;
		}

		for (final Constructor c : ((DataType) selector.getParameterSorts()[0].getSortSymbol()).getConstructors()) {
			if (Arrays.asList(c.getSelectors()).contains(selName)) {
				mSelectorMap.put(selName, c);
				return c;
			}
		}

		throw new AssertionError("No constructor for selector " + selector);
	}

	private static boolean isConstructorApp(Term term) {
		return term instanceof ApplicationTerm && ((ApplicationTerm) term).getFunction().isConstructor();
	}

	private class ConstrTerm {
		FunctionSymbol mConstr;
		CCTerm[] mArguments;

		public ConstrTerm(FunctionSymbol constr, CCTerm[] args) {
			mConstr = constr;
			mArguments = args;
		}
	}

	private Term createUniqueValue(ModelBuilder modelBuilder, FunctionSymbol constr, Term[] args) {
		boolean foundInfinite = false;
		for (int i = 0; i < args.length; i++) {
			if (args[i] == null) {
				final Sort sort = constr.getParameterSorts()[i];
				if (isInfinite(sort) && !foundInfinite) {
					args[i] = modelBuilder.getModel().extendFresh(sort);
					foundInfinite = true;
				} else {
					args[i] = modelBuilder.getModel().getSomeValue(sort);
				}
			}
		}
		return mTheory.term(constr, args);
	}

	public void fillInModel(ModelBuilder modelBuilder, List<Sort> sorts, LinkedHashMap<Sort, List<CCTerm>> repsBySort) {
		final LinkedHashMap<CCTerm, ConstrTerm> valueMap = new LinkedHashMap<>();
		for (final Sort sort: sorts) {
			assert sort.getSortSymbol().isDatatype();
			final List<CCTerm> ccTerms = repsBySort.get(sort);
			if (ccTerms == null) {
				continue;
			}
			for (final CCTerm ct : ccTerms) {
				CCTerm sharedTerm = ct.getSharedTerm();
				if (sharedTerm != null) {
					final FunctionSymbol constr = ((ApplicationTerm) sharedTerm.getFlatTerm()).getFunction();
					final CCTerm[] args = new CCTerm[constr.getParameterSorts().length];
					for (int i = constr.getParameterSorts().length - 1; i >= 0; i--) {
						final CCAppTerm app = (CCAppTerm) sharedTerm;
						args[i] = app.getArg();
						sharedTerm = app.getFunc();
					}
					valueMap.put(ct, new ConstrTerm(constr, args));
				} else {
					final Map<FunctionSymbol, CCAppTerm> selectorsAndTester = getSelectorsAndTesters(ct);
					final Constructor constr = findConstructorFromTester(ct, selectorsAndTester, modelBuilder);
					// we can use any constructor for which no tester exists. We use the first one.
					final String[] selectors = constr.getSelectors();
					final Sort[] argSorts = new Sort[selectors.length];
					final CCTerm[] args = new CCTerm[selectors.length];
					for (int i = 0; i < selectors.length; i++) {
						final FunctionSymbol selector = mTheory.getFunction(selectors[i], sort);
						argSorts[i] = selector.getReturnSort();
						args[i] = selectorsAndTester.get(selector);
					}
					final Sort consType = constr.needsReturnOverload() ? sort : null;
					final FunctionSymbol constrFunc = mTheory.getFunctionWithResult(constr.getName(), null, consType,
							argSorts);
					valueMap.put(ct, new ConstrTerm(constrFunc, args));
				}
			}
		}
		final ArrayDeque<CCTerm> todoStack = new ArrayDeque<>(valueMap.keySet());
		final ArrayDeque<CCTerm> path = new ArrayDeque<>();
		final HashSet<CCTerm> visited = new HashSet<>();
		while (!todoStack.isEmpty()) {
			final ArrayDeque<CCTerm> delayed = new ArrayDeque<>();
			CCTerm nextHole = null;
			Term[] nextHoleArgs = null;
			visited.clear();
			while (!todoStack.isEmpty()) {
				final CCTerm ct = todoStack.removeLast();
				if (modelBuilder.getModelValue(ct) != null) {
					// already has a model
					continue;
				}
				if (!visited.add(ct)) {
					// already visited but obviously delayed.
					delayed.addAll(path);
					path.clear();
					continue;
				}
				final ConstrTerm constrTerm = valueMap.get(ct);
				final Term[] argModels = new Term[constrTerm.mArguments.length];
				boolean undefined = false;
				boolean hasHole = false;
				for (int i = 0; i < argModels.length; i++) {
					CCTerm arg = constrTerm.mArguments[i];
					if (arg != null) {
						arg = arg.getRepresentative();
						argModels[i] = modelBuilder.getModelValue(arg);
						if (argModels[i] == null) {
							assert valueMap.containsKey(arg);
							path.add(ct);
							todoStack.addLast(arg);
							undefined = true;
							break;
						}
					} else {
						hasHole = true;
					}
				}
				if (!undefined) {
					if (hasHole) {
						delayed.addAll(path);
						if (nextHole == null) {
							nextHole = ct;
							nextHoleArgs = argModels;
						} else {
							delayed.add(ct);
						}
						path.clear();
					} else {
						final Term modelTerm = mTheory.term(constrTerm.mConstr, argModels);
						modelBuilder.setModelValue(ct, modelTerm);
						if (!path.isEmpty()) {
							final CCTerm nextFromPath = path.removeLast();
							visited.remove(nextFromPath);
							todoStack.addLast(nextFromPath);
						}
					}
				}
			}
			if (nextHole != null) {
				final ConstrTerm constrTerm = valueMap.get(nextHole);
				final Term modelTerm = createUniqueValue(modelBuilder, constrTerm.mConstr, nextHoleArgs);
				modelBuilder.setModelValue(nextHole, modelTerm);
				todoStack.addAll(delayed);
			} else {
				assert delayed.isEmpty();
			}
		}
	}

	private Constructor findConstructorFromTester(CCTerm ct, Map<FunctionSymbol, CCAppTerm> selectorsAndTesters, ModelBuilder modelBuilder) {
		final Sort sort = ct.getFlatTerm().getSort();
		final DataType datatype = (DataType) sort.getSortSymbol();
		Constructor suitableConstructor = null;
		for (final Constructor constr : datatype.getConstructors()) {
			final FunctionSymbol tester = mTheory.getFunctionWithResult(SMTLIBConstants.IS,
					new String[] { constr.getName() }, null, sort);
			final CCAppTerm testerApp = selectorsAndTesters.get(tester);
			if (testerApp == null) {
				// pick the first constructor for which there is no tester, if there are no true
				// testers.
				if (suitableConstructor == null) {
					suitableConstructor = constr;
				}
			} else if (modelBuilder.getModelValue(testerApp.getRepresentative()) == mTheory.mTrue) {
				// a true tester is always the right one.
				return constr;
			}
		}
		assert suitableConstructor != null : "Unpropagated dt_cases lemma";
		return suitableConstructor;
	}
}
