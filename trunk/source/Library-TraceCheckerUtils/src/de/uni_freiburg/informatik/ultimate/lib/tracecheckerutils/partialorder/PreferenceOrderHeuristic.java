/*
 * Copyright (C) 2022 Marcel Ebbinghaus
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class PreferenceOrderHeuristic<L extends IIcfgTransition<?>> {

	private Deque<IcfgEdge> mBFSWorklist;
	private Set<IcfgEdge> mFinished;
	private IIcfg<?> mIcfg;
	private List<String> mAllProcedures;
	private List<String> mAllLoopProcedures;
	private Set<IProgramVar> mEffectiveGlobalVars;
	private HashMap<String, ArrayList<Deque<IcfgEdge>>> mPathMap;
	private HashMap<String, HashMap<IProgramVar, Integer>> mLoopPathVarsMap;
	private HashMap<String, Set<IProgramVar>> mSharedVarsMap;
	private String mSequence;

	private final ManagedScript mMgdScript;

	private enum SearchType {
		MAIN, THREAD, LOOPSEARCH, LOOPBUILDPATH
	}

	public PreferenceOrderHeuristic(final IIcfg<?> icfg, final List<String> allProcedures,
			final Set<IProgramVar> effectiveGlobalVars, final HashMap<String, Set<IProgramVar>> sharedVars,
			final ManagedScript mgdScript) {
		this(icfg.getInitialNodes().stream().flatMap(a -> a.getOutgoingEdges().stream()).collect(Collectors.toSet()),
				mgdScript);
		mIcfg = icfg;
		mAllProcedures = allProcedures;
		mAllLoopProcedures = new ArrayList<>();
		mPathMap = new HashMap<>();
		mLoopPathVarsMap = new HashMap<>();
		mEffectiveGlobalVars = effectiveGlobalVars;
		mSharedVarsMap = sharedVars;
	}

	// TODO Why are there 2 constructors? And why does one of them only initialize some of the fields? Dangerous!
	public <T extends IcfgEdge> PreferenceOrderHeuristic(final Collection<T> edges, final ManagedScript mgdScript) {
		mBFSWorklist = new ArrayDeque<>();
		mBFSWorklist.addAll(edges);
		mFinished = new HashSet<>(mBFSWorklist);
		mMgdScript = mgdScript;
	}

	private void applyBFS(final IcfgLocation start, final SearchType searchType, final IcfgLocation goal) {
		final Deque<IcfgEdge> worklist = new ArrayDeque<>();
		final Set<IcfgEdge> outgoingStartEdges = new HashSet<>();
		// for the Loop-Search, only search within the body without marking the nodes as finished
		/*
		 * if (searchType.equals(SearchType.THREAD) && mIcfg.getLoopLocations().contains(start)) { BFS(start,
		 * SearchType.LOOPSEARCH, start); }
		 */
		if (searchType.equals(SearchType.LOOPSEARCH)) {
			start.getOutgoingEdges().stream().forEachOrdered(outgoingStartEdges::add);
		} else {
			start.getOutgoingEdges().stream().filter(mFinished::add).forEachOrdered(outgoingStartEdges::add);
		}
		worklist.addAll(outgoingStartEdges);
		final HashMap<IcfgEdge, IcfgEdge> parentMap = new HashMap<>();
		for (final IcfgEdge edge : outgoingStartEdges) {
			parentMap.put(edge, null);
		}
		final String currentProcedure = start.getProcedure();
		while (!worklist.isEmpty()) {
			final IcfgEdge current = worklist.removeFirst();
			// remember which variables were accessed to determine the shared variables
			final Set<IProgramVar> currentVars = new HashSet<>();
			currentVars.addAll(current.getTransformula().getInVars().keySet());
			currentVars.addAll(current.getTransformula().getOutVars().keySet());
			final IcfgLocation target = current.getTarget();
			if (isGoal(current, searchType, goal)) {
				switch (searchType) {
				case MAIN:
					applyBFS(target, SearchType.THREAD, null);
					break;
				case THREAD:
					// only search for the loopEntryEdge first
					applyBFS(target, SearchType.LOOPSEARCH, target);
					break;
				case LOOPSEARCH:
					// extract the loopEntryEdge and continue the search
					final IcfgEdge loopEntryEdge = buildPath(parentMap, current).getFirst();
					if (loopEntryEdge.getSource().equals(start)) {
						applyBFS(loopEntryEdge.getSource(), SearchType.LOOPBUILDPATH, loopEntryEdge.getSource());
					} else {
						mFinished.add(loopEntryEdge);
						applyBFS(loopEntryEdge.getTarget(), SearchType.LOOPBUILDPATH, loopEntryEdge.getSource());
					}
					break;
				case LOOPBUILDPATH:
					// save the path and do the computation at the end
					final Deque<IcfgEdge> path = buildPath(parentMap, current);
					ArrayList<Deque<IcfgEdge>> pathList = new ArrayList<>();
					if (mPathMap.get(currentProcedure) != null) {
						pathList = mPathMap.get(currentProcedure);

					}
					pathList.add(path);
					mPathMap.put(currentProcedure, pathList);

					applyBFS(target, SearchType.THREAD, null);
					break;
				default:

				}
			} else if (target.getProcedure() == currentProcedure) {
				// continue the search within the current Procedure
				final Set<IcfgEdge> outgoingEdges = new HashSet<>();
				if (searchType.equals(SearchType.LOOPSEARCH)) {
					target.getOutgoingEdges().stream().forEachOrdered(outgoingEdges::add);
				} else {
					target.getOutgoingEdges().stream().filter(mFinished::add).forEachOrdered(outgoingEdges::add);
				}
				worklist.addAll(outgoingEdges);
				for (final IcfgEdge edge : outgoingEdges) {
					parentMap.put(edge, current);
				}
			}
		}
	}

	private boolean isGoal(final IcfgEdge current, final SearchType searchType, final IcfgLocation goal) {
		switch (searchType) {
		case MAIN:
			return !current.getSucceedingProcedure().equals(current.getPrecedingProcedure());
		case THREAD:
			return mIcfg.getLoopLocations().contains(current.getTarget());
		default:
			return current.getTarget().equals(goal);
		}
	}

	private Deque<IcfgEdge> buildPath(final HashMap<IcfgEdge, IcfgEdge> parentMap, IcfgEdge current) {
		final Deque<IcfgEdge> path = new ArrayDeque<>();
		while (current != null) {
			path.addFirst(current);
			current = parentMap.get(current);
		}
		return path;
	}

	public void computeParameterizedOrder() {
		for (final String Procedure : mAllProcedures) {
			final IcfgLocation initialLocation = mIcfg.getProcedureEntryNodes().get(Procedure);
			if (mIcfg.getLoopLocations().contains(initialLocation)) {
				// covers the case where the thread starts with a loop
				applyBFS(initialLocation, SearchType.LOOPSEARCH, initialLocation);
			} else {
				// covers all other cases
				applyBFS(initialLocation, SearchType.THREAD, null);
			}
		}

		computeLoopVarAccesses();
		mMgdScript.lock(this);
		mMgdScript.push(this, 1);
		// SMTInterpol SMTInterpol = new SMTInterpol();
		// SMTInterpol.setLogic("QF_LIA");
		// String just for debugging
		// String SMTScriptString = "(set-logic QF_LIA)\r\n";
		// for (final String procedure : mAllLoopProcedures) {
		// SMTScriptString += String.format("(declare-fun %s () Int)\r\n", procedure);
		// SMTInterpol.declareFun(procedure, new Sort[0], SMTInterpol.sort("Int"));
		// mMgdScript.declareFun(this, procedure, new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		// }
		var procConstants = declareProcedureConstants(mAllLoopProcedures);
		final var script = mMgdScript.getScript();

		final HashMap<Term, Integer> termEvaluationMap = new HashMap<>();

		for (final String fstProcedure : mAllLoopProcedures) {
			final int fstIndex = mAllLoopProcedures.indexOf(fstProcedure);
			if (fstIndex < mAllLoopProcedures.size() - 1) {
				for (int sndIndex = fstIndex + 1; sndIndex < mAllLoopProcedures.size(); sndIndex++) {
					// calculate the accesses on shared vars
					final String sndProcedure = mAllLoopProcedures.get(sndIndex);
					int fstSharedAccesses = 0;
					int sndSharedAccesses = 0;
					final HashMap<IProgramVar, Integer> fstVarMap = mLoopPathVarsMap.get(fstProcedure);
					final HashMap<IProgramVar, Integer> sndVarMap = mLoopPathVarsMap.get(sndProcedure);
					final Set<IProgramVar> sharedVars = new HashSet<>(mSharedVarsMap.get(fstProcedure));
					sharedVars.retainAll(mSharedVarsMap.get(sndProcedure));
					for (final IProgramVar var : sharedVars) {
						if (fstVarMap.containsKey(var)) {
							fstSharedAccesses += fstVarMap.get(var);
						}
						if (sndVarMap.containsKey(var)) {
							sndSharedAccesses += sndVarMap.get(var);
						}
					}
					// SMTScriptString += String.format("(assert (= (* %d %s) (* %d %s)))\r\n", fstSharedAccesses,
					// fstProcedure, sndSharedAccesses, sndProcedure);
					/*
					 * Term fstSA = SMTInterpol.numeral(Integer.toString(fstSharedAccesses)); Term sndSA =
					 * SMTInterpol.numeral(Integer.toString(sndSharedAccesses)); Term fstP =
					 * SMTInterpol.term(fstProcedure); Term sndP = SMTInterpol.term(sndProcedure); Term fstMult =
					 * SMTInterpol.term("*", fstSA, fstP); Term sndMult = SMTInterpol.term("*", sndSA, sndP); Term
					 * equation = SMTInterpol.term("=", fstMult, sndMult); SMTInterpol.assertTerm(equation);
					 */

					final Rational fstSA = SmtUtils.toRational(fstSharedAccesses);
					final Rational sndSA = SmtUtils.toRational(sndSharedAccesses);
					// final Term fstP = script.term(fstProcedure);
					// final Term sndP = script.term(sndProcedure);
					final Term fstMul = SmtUtils.mul(script, fstSA, procConstants.get(fstProcedure));
					final Term sndMul = SmtUtils.mul(script, sndSA, procConstants.get(sndProcedure));
					final Term equation = SmtUtils.equality(script, fstMul, sndMul);
					mMgdScript.assertTerm(this, equation);
				}
			}
			// SMTScriptString += String.format("(assert (< 0 %s))\r\n", fstProcedure);

			/*
			 * Term procedure = SMTInterpol.term(fstProcedure); Term zero = SMTInterpol.numeral("0"); Term condition =
			 * SMTInterpol.term("<", zero, procedure); SMTInterpol.assertTerm(condition);
			 */

			// final Term procedure = script.term(fstProcedure);
			final Term zero = SmtUtils.toRational(0).toTerm(script.sort(SmtSortUtils.INT_SORT));
			final Term condition = SmtUtils.less(script, zero, procConstants.get(fstProcedure));
			mMgdScript.assertTerm(this, condition);

			termEvaluationMap.put(procConstants.get(fstProcedure), null);
		}
		// try to solve equation system
		// SMTScriptString += "(check-sat)\r\n" + "(get-model)";
		String sequence = "";
		final var result = mMgdScript.checkSat(this);

		// !SMTInterpol.checkSat().equals(Script.LBool.SAT)
		// !script.checkSat() == LBool.SAT
		if (result != LBool.SAT) {
			// if not solvable, then calculate the accesses on shared vars for all procedures at once
			termEvaluationMap.clear();

			// SMTInterpol.resetAssertions();
			// SMTInterpol.declareFun("dummy", new Sort[0], SMTInterpol.sort("Int"));
			mMgdScript.pop(this, 1);
			mMgdScript.push(this, 1);

			procConstants = declareProcedureConstants(mAllLoopProcedures);

			// MScript.setLogic("(set-logic QF_LIA)\r\n");
			// script.declareFun("dummy", new Sort[0], script.sort("Int"));
			final var dummy = SmtUtils.buildNewConstant(script, "dummy", SmtSortUtils.INT_SORT);

			for (final String procedure : mAllLoopProcedures) {
				int sharedAccesses = 0;
				final HashMap<IProgramVar, Integer> varMap = mLoopPathVarsMap.get(procedure);
				for (final IProgramVar var : varMap.keySet()) {
					if (mEffectiveGlobalVars.contains(var)) {
						sharedAccesses += varMap.get(var);
					}
				}
				/*
				 * Term procedureSA = SMTInterpol.numeral(Integer.toString(sharedAccesses));
				 * SMTInterpol.declareFun(procedure, new Sort[0], SMTInterpol.sort("Int")); Term procedureTerm =
				 * SMTInterpol.term(procedure); Term mult = SMTInterpol.term("*", procedureSA, procedureTerm); Term
				 * dummy = SMTInterpol.term("dummy"); Term equation = SMTInterpol.term("=", dummy, mult);
				 * SMTInterpol.assertTerm(equation); Term zero = SMTInterpol.numeral("0"); Term condition =
				 * SMTInterpol.term("<", zero, procedureTerm); SMTInterpol.assertTerm(condition);
				 */

				final Rational procedureSA = SmtUtils.toRational(sharedAccesses);
				// script.declareFun(procedure, new Sort[0], script.sort("Int"));
				// final Term procedureTerm = script.term(procedure);
				// final Term dummy = script.term("dummy");
				final Term mult = SmtUtils.mul(script, procedureSA, procConstants.get(procedure));
				final Term equation = SmtUtils.equality(script, dummy, mult);
				mMgdScript.assertTerm(this, equation);

				final Term zero = SmtUtils.toRational(0).toTerm(script.sort(SmtSortUtils.INT_SORT));
				final Term condition = SmtUtils.less(script, zero, procConstants.get(procedure));
				mMgdScript.assertTerm(this, condition);

				termEvaluationMap.put(procConstants.get(procedure), null);
			}

			// SMTInterpol.checkSat();
			mMgdScript.checkSat(this);
		}
		// Model model = SMTInterpol.getModel();
		// final Model model = script.getModel();
		// final ArrayList<Term> termList = new ArrayList<>();

		final var termValues = mMgdScript.getValue(this, termEvaluationMap.keySet().toArray(Term[]::new));
		for (final Term term : termEvaluationMap.keySet()) {
			// final Term value = model.evaluate(term);
			final Term value = termValues.get(term);
			final var rational = SmtUtils.tryToConvertToLiteral(value);
			assert rational != null && rational.isIntegral();

			termEvaluationMap.put(term, rational.numerator().intValue());
			// termList.add(term);
		}

		if (!mAllLoopProcedures.isEmpty()) {
			for (final Term term : termEvaluationMap.keySet()) {
				final int value = termEvaluationMap.get(term);
				final int maxStep = value;
				sequence += String.format("%d,%d ", mAllProcedures.indexOf(term.toString()), maxStep);
			}
		}

		final var remainingProcedures =
				mAllProcedures.stream().filter(p -> !mAllLoopProcedures.contains(p)).collect(Collectors.toList());
		for (final String procedure : remainingProcedures) {
			sequence += String.format("%d,1 ", mAllProcedures.indexOf(procedure));
		}
		sequence = sequence.substring(0, sequence.length() - 1);
		mSequence = sequence;
		mMgdScript.pop(this, 1);
		mMgdScript.unlock(this);
	}

	private Map<String, Term> declareProcedureConstants(final List<String> procedures) {
		return procedures.stream().collect(Collectors.toMap(Function.identity(), this::makeProcedureConstant));
	}

	private Term makeProcedureConstant(final String name) {
		return SmtUtils.buildNewConstant(mMgdScript.getScript(), name, SmtSortUtils.INT_SORT);
	}

	private void computeLoopVarAccesses() {
		// compute the amount of variable accesses in the loop for each procedure
		for (final String procedure : mAllProcedures) {
			final ArrayList<Deque<IcfgEdge>> pathList = mPathMap.get(procedure);
			if (pathList != null) {
				mAllLoopProcedures.add(procedure);
				final Deque<IcfgEdge> loopPath = pathList.get(0);
				final HashMap<IProgramVar, Integer> varMap = new HashMap<>();
				for (final IcfgEdge edge : loopPath) {
					final Set<IProgramVar> edgeVars = new HashSet<>();
					edgeVars.addAll(edge.getTransformula().getInVars().keySet());
					edgeVars.addAll(edge.getTransformula().getOutVars().keySet());
					for (final IProgramVar var : edgeVars) {
						if (varMap.containsKey(var)) {
							final Integer value = varMap.get(var) + 1;
							varMap.put(var, value);
						} else {
							varMap.put(var, 1);
						}
					}
				}
				mLoopPathVarsMap.put(procedure, varMap);
			}
		}
	}

	public String getParameterizedOrderSequence() {
		return mSequence;
	}

	public Set<IProgramVar> getEffectiveGlobalVars() {
		return mEffectiveGlobalVars;
	}
}
