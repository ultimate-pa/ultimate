/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.ExternalSolver;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 *
 * @author Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 *
 */

public class FeasibilityFilter<ACTION, LOC> implements IFilter<ACTION, LOC> {

	private final Set<ACTION> mAllReads;
	private final Map<ACTION, String> mAction2Function;
	private final Map<IProgramVarOrConst, String> mVariable2Function;

	private int mActCounter;
	private final int mVarCounter;

	private final Script mScript;

	private ITransitionProvider<ACTION, LOC> mTransitionProvider;

	private final Map<FeasibilityFilter.Sorts, String> mSorts;
	private final Map<FeasibilityFilter.Relations, String> mRelations;

	private enum Relations {
		DOMINATES, NOT_REACHABLE_FROM, THCREATES, THJOINS, ISLOAD, ISSTORE, MHB, READS_FROM
	}

	private enum Sorts {
		ACTION, VARIABLE
	}

	public FeasibilityFilter(final IUltimateServiceProvider services) {
		final SolverSettings solverSettings =
				SolverBuilder.constructSolverSettings().setUseExternalSolver(ExternalSolver.Z3, Logics.HORN)
						.setSolverMode(SolverMode.External_DefaultMode).setDumpSmtScriptToFile(true,
								"/home/jo/Documents/Studium/Bachelor/6.Semester/Bachelor-Projekt", "script", false);
		// "/home/jo/Documents/Studium/Bachelor/6.Semester/Bachelor-Projekt"

		mScript = SolverBuilder.buildAndInitializeSolver(services, solverSettings, "HornClauseSolver");

		mAllReads = new HashSet<>();
		mAction2Function = new HashMap<>();
		mVariable2Function = new HashMap<>();
		mActCounter = 0;
		mVarCounter = 0;

		mSorts = new HashMap<>();
		mRelations = new HashMap<>();

		defineNames();
	}

	@Override
	public boolean evaluate(final Map<LOC, Set<ACTION>> read2Writes) {
		mScript.push(1);
		for (final var entry : read2Writes.entrySet()) {
			for (final ACTION potentialRead : mTransitionProvider.getSuccessorActions(entry.getKey())) {
				if (!mAllReads.contains(potentialRead)) {
					// Not every outgoing edge from LOC must be a read!
					continue;
				}
				String read = mAction2Function.get(potentialRead);
				if (read == null) {
					read = declareFunctionforAction(potentialRead, mScript.sort(mSorts.get(Sorts.ACTION)));
				}
				for (final ACTION action : entry.getValue()) {
					String write = mAction2Function.get(action);
					if (write == null) {
						write = declareFunctionforAction(action, mScript.sort(mSorts.get(Sorts.ACTION)));
					}
					mScript.assertTerm(mScript.term(mRelations.get(Relations.READS_FROM), mScript.term(read),
							mScript.term(write)));
				}
			}
		}
		final LBool result = mScript.checkSat();
		mScript.pop(1);
		if (result == LBool.UNSAT) {
			return false;
		}
		// UNKNOWN or SAT
		return true;
	}

	public void setTransitionProvider(final ITransitionProvider<ACTION, LOC> transitionProvider) {
		mTransitionProvider = transitionProvider;
	}

	public void initializeProgramConstraints(final List<HashRelation<ACTION, ACTION>> programOrderConstraints,
			final HashRelation<ACTION, IProgramVarOrConst> isLoad,
			final HashRelation<ACTION, IProgramVarOrConst> isStore, final Set<ACTION> allReads) {

		mAllReads.addAll(allReads);
		// Declare Sorts
		mScript.declareSort(mSorts.get(Sorts.ACTION), 0);
		mScript.declareSort(mSorts.get(Sorts.VARIABLE), 0);
		final Sort action = mScript.sort(mSorts.get(Sorts.ACTION));
		final Sort variable = mScript.sort(mSorts.get(Sorts.VARIABLE));
		final Sort bool = mScript.sort("Bool");

		// Declare Functions (Relations)
		final List<Sort> actAct = new ArrayList<>();
		actAct.add(action);
		actAct.add(action);
		final Sort[] paramsActAct = actAct.toArray(new Sort[actAct.size()]);
		mScript.declareFun(mRelations.get(Relations.DOMINATES), paramsActAct, bool);
		mScript.declareFun(mRelations.get(Relations.NOT_REACHABLE_FROM), paramsActAct, bool);
		mScript.declareFun(mRelations.get(Relations.MHB), paramsActAct, bool);
		mScript.declareFun(mRelations.get(Relations.THCREATES), paramsActAct, bool);
		mScript.declareFun(mRelations.get(Relations.THJOINS), paramsActAct, bool);
		mScript.declareFun(mRelations.get(Relations.READS_FROM), paramsActAct, bool);
		final List<Sort> actVar = new ArrayList<>();
		actVar.add(action);
		actVar.add(variable);
		final Sort[] paramsActVar = actVar.toArray(new Sort[actVar.size()]);
		mScript.declareFun(mRelations.get(Relations.ISLOAD), paramsActVar, bool);
		mScript.declareFun(mRelations.get(Relations.ISSTORE), paramsActVar, bool);

		// add Rules from Paper
		mScript.assertTerm(dominationRule(action));
		mScript.assertTerm(forkRule(action));
		mScript.assertTerm(joinRule(action));
		mScript.assertTerm(transitivity(action));
		mScript.assertTerm(readsFromOne(action, variable));
		mScript.assertTerm(canNotReadFrom(action));
		mScript.assertTerm(readsFromTwo(action, variable));

		// Add Assertions from Program
		final List<String> order = new ArrayList<>();
		order.add(mRelations.get(Relations.DOMINATES));
		order.add(mRelations.get(Relations.NOT_REACHABLE_FROM));
		order.add(mRelations.get(Relations.THCREATES));
		order.add(mRelations.get(Relations.THJOINS));

		if (order.size() != programOrderConstraints.size()) {
			throw new IllegalArgumentException("invalid params");
		}
		for (int i = 0; i < order.size(); i++) {
			addProgramOrderConstraints(programOrderConstraints.get(i), order.get(i), action);
		}

		addVariableConstraints(isLoad, mRelations.get(Relations.ISLOAD), action, variable);
		addVariableConstraints(isStore, mRelations.get(Relations.ISSTORE), action, variable);

		mScript.checkSat();
	}

	private void defineNames() {
		mRelations.put(Relations.DOMINATES, "dominates");
		mRelations.put(Relations.NOT_REACHABLE_FROM, "notReachableFrom");
		mRelations.put(Relations.THCREATES, "thCreates");
		mRelations.put(Relations.THJOINS, "thJoins");
		mRelations.put(Relations.ISLOAD, "isLoad");
		mRelations.put(Relations.ISSTORE, "isStore");
		mRelations.put(Relations.MHB, "mustHappenBefore");
		mRelations.put(Relations.READS_FROM, "readsFrom");

		mSorts.put(Sorts.ACTION, "Action");
		mSorts.put(Sorts.VARIABLE, "Variable");

	}

	private void addProgramOrderConstraints(final HashRelation<ACTION, ACTION> relation, final String relationName,
			final Sort action) {
		for (final var entry : relation.entrySet()) {
			String one = mAction2Function.get(entry.getKey());
			if (one == null) {
				one = declareFunctionforAction(entry.getKey(), action);
			}
			for (final var value : entry.getValue()) {
				String two = mAction2Function.get(value);
				if (two == null) {
					two = declareFunctionforAction(value, action);
				}
				mScript.assertTerm(mScript.term(relationName, mScript.term(one), mScript.term(two)));
			}
		}
	}

	private void addVariableConstraints(final HashRelation<ACTION, IProgramVarOrConst> relation,
			final String relationName, final Sort action, final Sort variable) {
		for (final var entry : relation.entrySet()) {
			String one = mAction2Function.get(entry.getKey());
			if (one == null) {
				one = declareFunctionforAction(entry.getKey(), action);
			}
			for (final var value : entry.getValue()) {
				String two = mVariable2Function.get(value);
				if (two == null) {
					two = declareFunctionforVariable(value, variable);
				}
				mScript.assertTerm(mScript.term(relationName, mScript.term(one), mScript.term(two)));
			}
		}
	}

	private Term dominationRule(final Sort sort) {
		final TermVariable a = mScript.variable("a", sort);
		final TermVariable b = mScript.variable("b", sort);
		return forAll(implication(dominates(a, b), notReachable(a, b), mustHappenBefore(a, b)));
	}

	private Term forkRule(final Sort sort) {
		final TermVariable a = mScript.variable("a", sort);
		final TermVariable b = mScript.variable("b", sort);
		// Rule from Paper
		// return forAll(implication(forks(a, b), mustHappenBefore(a, b)));
		// Adapted Rule version
		return forAll(exists(implication(forks(a, b), mustHappenBefore(a, b)), a));
	}

	private Term joinRule(final Sort sort) {
		final TermVariable a = mScript.variable("a", sort);
		final TermVariable b = mScript.variable("b", sort);
		return forAll(implication(joins(a, b), mustHappenBefore(b, a)));
	}

	private Term readsFromOne(final Sort action, final Sort variable) {
		final TermVariable l = mScript.variable("l", action);
		final TermVariable s1 = mScript.variable("s1", action);
		final TermVariable s2 = mScript.variable("s2", action);
		final TermVariable x = mScript.variable("x", variable);
		return forAll(implication(readsFrom(l, s1), mustHappenBefore(s1, s2), isLoad(l, x), isStore(s1, x),
				isStore(s2, x), mustHappenBefore(l, s2)));
	}

	private Term transitivity(final Sort sort) {
		final TermVariable a = mScript.variable("a", sort);
		final TermVariable b = mScript.variable("b", sort);
		final TermVariable c = mScript.variable("c", sort);
		return forAll(implication(mustHappenBefore(a, b), mustHappenBefore(b, c), mustHappenBefore(a, c)));
	}

	private Term canNotReadFrom(final Sort sort) {
		final TermVariable a = mScript.variable("a", sort);
		final TermVariable b = mScript.variable("b", sort);
		return forAll(implication(mustHappenBefore(a, b), readsFrom(a, b), mScript.term("false")));
	}

	private Term readsFromTwo(final Sort action, final Sort variable) {
		final TermVariable l1 = mScript.variable("l1", action);
		final TermVariable l2 = mScript.variable("l2", action);
		final TermVariable s1 = mScript.variable("s1", action);
		final TermVariable s2 = mScript.variable("s2", action);
		final TermVariable x = mScript.variable("x", variable);
		final Term condition =
				mScript.term("and", readsFrom(l1, s1), mustHappenBefore(l1, s2), mustHappenBefore(s2, l2),
						isLoad(l1, x), isLoad(l2, x), isStore(s1, x), isStore(s2, x), readsFrom(l2, s1));
		return forAll(implication(condition, mScript.term("false")));
	}

	private Term dominates(final Term a, final Term b) {
		if (a.getSort() == mScript.sort(mSorts.get(Sorts.ACTION))
				&& a.getSort() == mScript.sort(mSorts.get(Sorts.ACTION))) {
			return mScript.term(mRelations.get(Relations.DOMINATES), a, b);
		}
		throw new UnsupportedOperationException("Wrong Sort of Variables");

	}

	private Term notReachable(final Term a, final Term b) {
		if (a.getSort() == mScript.sort(mSorts.get(Sorts.ACTION))
				&& a.getSort() == mScript.sort(mSorts.get(Sorts.ACTION))) {
			return mScript.term(mRelations.get(Relations.NOT_REACHABLE_FROM), a, b);
		}
		throw new UnsupportedOperationException("Wrong Sort of Variables");
	}

	private Term mustHappenBefore(final Term a, final Term b) {
		if (a.getSort() == mScript.sort(mSorts.get(Sorts.ACTION))
				&& a.getSort() == mScript.sort(mSorts.get(Sorts.ACTION))) {
			return mScript.term(mRelations.get(Relations.MHB), a, b);
		}
		throw new UnsupportedOperationException("Wrong Sort of Variables");
	}

	private Term forks(final Term fork, final Term entry) {
		if (fork.getSort() == mScript.sort(mSorts.get(Sorts.ACTION))
				&& entry.getSort() == mScript.sort(mSorts.get(Sorts.ACTION))) {
			return mScript.term(mRelations.get(Relations.THCREATES), fork, entry);
		}
		throw new UnsupportedOperationException("Wrong Sort of Variables");
	}

	private Term joins(final Term join, final Term exit) {
		if (join.getSort() == mScript.sort(mSorts.get(Sorts.ACTION))
				&& exit.getSort() == mScript.sort(mSorts.get(Sorts.ACTION))) {

			return mScript.term(mRelations.get(Relations.THJOINS), join, exit);
		}
		throw new UnsupportedOperationException("Wrong Sort of Variables");
	}

	private Term readsFrom(final Term read, final Term write) {
		if (read.getSort() == mScript.sort(mSorts.get(Sorts.ACTION))
				&& write.getSort() == mScript.sort(mSorts.get(Sorts.ACTION))) {
			return mScript.term(mRelations.get(Relations.READS_FROM), read, write);
		}
		throw new UnsupportedOperationException("Wrong Sort of Variables");
	}

	private Term isLoad(final Term read, final Term variable) {
		if (read.getSort() == mScript.sort(mSorts.get(Sorts.ACTION))
				&& variable.getSort() == mScript.sort(mSorts.get(Sorts.VARIABLE))) {
			return mScript.term(mRelations.get(Relations.ISLOAD), read, variable);
		}
		throw new UnsupportedOperationException("Wrong Sort of Variables");
	}

	private Term isStore(final Term write, final Term variable) {
		if (write.getSort() == mScript.sort(mSorts.get(Sorts.ACTION))
				&& variable.getSort() == mScript.sort(mSorts.get(Sorts.VARIABLE))) {
			return mScript.term(mRelations.get(Relations.ISSTORE), write, variable);
		}
		throw new UnsupportedOperationException("Wrong Sort of Variables");
	}

	private Term implication(final Term... terms) {
		return mScript.term("=>", terms);
	}

	private Term forAll(final Term term) {
		// not sure what pattern exaclty does
		// SmtUtils.quantifier(script, quantifier, vars, subformula)
		final Set<Term> termCollection = new HashSet<>();
		termCollection.add(term);
		return SmtUtils.quantifier(mScript, 1, SmtUtils.getFreeVars(termCollection), term);
	}

	private Term exists(final Term term, final TermVariable variable) {
		final Set<TermVariable> variables = new HashSet<>();
		variables.add(variable);
		return SmtUtils.quantifier(mScript, 0, variables, term);
	}

	private String declareFunctionforAction(final ACTION item, final Sort action) {
		final String procedure = mTransitionProvider.getProcedureName(item);
		final String name = item.toString() + "_" + procedure + "_" + String.valueOf(mActCounter);
		mScript.declareFun(name, new Sort[0], action);
		mAction2Function.put(item, name);
		mActCounter++;
		return name;
	}

	private String declareFunctionforVariable(final IProgramVarOrConst item, final Sort variable) {
		// assumption, no two global variables have the same name
		final String name = item.toString();
		mScript.declareFun(name, new Sort[0], variable);
		mVariable2Function.put(item, name);
		return name;
	}
}