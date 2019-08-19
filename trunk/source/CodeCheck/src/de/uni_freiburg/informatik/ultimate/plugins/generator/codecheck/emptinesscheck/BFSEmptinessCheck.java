/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CodeCheck plug-in.
 * 
 * The ULTIMATE CodeCheck plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CodeCheck plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CodeCheck plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CodeCheck plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CodeCheck plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.emptinesscheck;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AnnotatedProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.DummyCodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.EmptyStackSymbol;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class BFSEmptinessCheck implements IEmptinessCheck {
	private static final int BAD_NESTING_RELATION_INIT = -7;

	private ArrayDeque<AppDoubleDecker> mOpenNodes;
	private HashSet<AppDoubleDecker> mVisitedNodes;
	private HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>> mSummaryEdges;
	private HashMap<Pair<AnnotatedProgramPoint, AnnotatedProgramPoint>, AppDoubleDecker> mSummaryEdgeToReturnSucc;

	private final ILogger mLogger;

	public BFSEmptinessCheck(final ILogger logger) {
		mLogger = logger;
	}

	/**
	 * Search for a nested error path within the graph with the given root. IIcfgReturnTransition<?,?> null if there is
	 * none.
	 * 
	 * @param root
	 * @return
	 */
	@Override
	public NestedRun<IIcfgTransition<?>, AnnotatedProgramPoint> checkForEmptiness(final AnnotatedProgramPoint root) {
		mOpenNodes = new ArrayDeque<>();
		mVisitedNodes = new HashSet<>();

		mSummaryEdges = new HashMap<>();
		mSummaryEdgeToReturnSucc = new HashMap<>();

		final EmptyStackSymbol emptyStackSymbol = new EmptyStackSymbol();

		mOpenNodes.add(new AppDoubleDecker(root, emptyStackSymbol, new Stack<IIcfgCallTransition<?>>(),
				new Stack<AnnotatedProgramPoint>()));
		Pair<AnnotatedProgramPoint[], NestedWord<IIcfgTransition<?>>> returnedPath = null;

		while (!mOpenNodes.isEmpty() && returnedPath == null) {
			final AppDoubleDecker currentAdd = mOpenNodes.pollFirst();
			mVisitedNodes.add(currentAdd);

			for (final AnnotatedProgramPoint app : currentAdd.mTop.getOutgoingNodes()) {
				// IIcfgTransition<?> edge = currentAdd.top.getOutgoingEdgeLabel(app); //FIXME
				final IIcfgTransition<?> edge = null;

				if (edge instanceof Summary) {
					continue;
				}

				AppDoubleDecker newAdd = null;

				if (!(edge instanceof IIcfgCallTransition<?> || edge instanceof IIcfgReturnTransition<?, ?>)) {

					newAdd = new AppDoubleDecker(app, currentAdd.mBot,
							(Stack<IIcfgCallTransition<?>>) currentAdd.mCallStack.clone(),
							(Stack<AnnotatedProgramPoint>) currentAdd.mCallPredStack.clone());
					if (returnedPath == null) {
						returnedPath = openNewNode(currentAdd, app, edge, newAdd);
					}

				} else if (edge instanceof IIcfgCallTransition<?>) {

					newAdd = new AppDoubleDecker(app, currentAdd.mTop,
							(Stack<IIcfgCallTransition<?>>) currentAdd.mCallStack.clone(),
							(Stack<AnnotatedProgramPoint>) currentAdd.mCallPredStack.clone());
					newAdd.mCallStack.add((IIcfgCallTransition<?>) edge);
					newAdd.mCallPredStack.add(currentAdd.mBot);

					if (returnedPath == null) {
						returnedPath = openNewNode(currentAdd, app, edge, newAdd);
					}

				} else if (edge instanceof IIcfgReturnTransition<?, ?>) {
					final Stack<IIcfgCallTransition<?>> currentCallStack =
							(Stack<IIcfgCallTransition<?>>) currentAdd.mCallStack.clone();
					final Stack<AnnotatedProgramPoint> currentCpStack =
							(Stack<AnnotatedProgramPoint>) currentAdd.mCallPredStack.clone();

					final IIcfgCallTransition<?> poppedCall = currentCallStack.pop();
					final AnnotatedProgramPoint callPredPred = currentCpStack.pop();

					if (!((IIcfgReturnTransition<?, ?>) edge).getCorrespondingCall().equals(poppedCall)) {
						continue;
					}

					newAdd = new AppDoubleDecker(app, callPredPred, currentCallStack, currentCpStack);

					addSummaryEdge(currentAdd.mBot, app);
					final Pair<AnnotatedProgramPoint, AnnotatedProgramPoint> pairToAdd =
							new Pair<>(currentAdd.mBot, app); // rausgezogen
																// fuer
																// debugging
					mSummaryEdgeToReturnSucc.put(pairToAdd, newAdd);
					if (returnedPath == null) {
						returnedPath = openNewNode(currentAdd, app, edge, newAdd);
					}
				}
			}

			// also unwind summaryEdges
			final HashSet<AnnotatedProgramPoint> targets = mSummaryEdges.get(currentAdd.mTop);
			if (targets != null) {
				for (final AnnotatedProgramPoint target : targets) {
					final AppDoubleDecker newAdd = new AppDoubleDecker(target, currentAdd.mBot,
							(Stack<IIcfgCallTransition<?>>) currentAdd.mCallStack.clone(),
							(Stack<AnnotatedProgramPoint>) currentAdd.mCallPredStack.clone());
					if (returnedPath == null) {
						// convention: AddEdges which are summaries are labeled "null"
						returnedPath = openNewNode(currentAdd, target, new DummyCodeBlock(), newAdd);
					}
				}
			}
		}
		return returnedPath == null ? null
				: new NestedRun<>(returnedPath.getSecond(), new ArrayList<>(Arrays.asList(returnedPath.getFirst())));
	}

	private void addSummaryEdge(final AnnotatedProgramPoint bot, final AnnotatedProgramPoint app) {
		HashSet<AnnotatedProgramPoint> targets = mSummaryEdges.get(bot);
		if (targets == null) {
			targets = new HashSet<>();
		}
		targets.add(app);
		mSummaryEdges.put(bot, targets);
	}

	private Pair<AnnotatedProgramPoint[], NestedWord<IIcfgTransition<?>>> openNewNode(final AppDoubleDecker currentAdd,
			final AnnotatedProgramPoint app, final IIcfgTransition<?> edge, final AppDoubleDecker newAdd) {
		if (!mVisitedNodes.contains(newAdd)) {
			final AddEdge newAddEdge = new AddEdge(currentAdd, newAdd, edge);
			newAdd.mInEdge = newAddEdge;
			currentAdd.mOutEdges.add(newAddEdge);
			newAdd.setPathToRoot();

			if (app.isErrorLocation()) {
				return reconstructPath(newAdd);
			}

			mOpenNodes.add(newAdd);
		}
		return null;
	}

	private Pair<AnnotatedProgramPoint[], NestedWord<IIcfgTransition<?>>>
			reconstructPath(final AppDoubleDecker errorAdd) {
		ArrayDeque<AnnotatedProgramPoint> errorPath = new ArrayDeque<>();
		ArrayDeque<IIcfgTransition<?>> errorTrace = new ArrayDeque<>();

		AppDoubleDecker currentAdd = errorAdd;
		AddEdge currentInEdge = errorAdd.mInEdge;

		while (currentInEdge != null) {
			errorPath.addFirst(currentAdd.mTop);
			errorTrace.addFirst(currentInEdge.mLabel);

			currentAdd = currentInEdge.mSource;
			currentInEdge = currentAdd.mInEdge;
		}
		errorPath.addFirst(currentAdd.mTop);

		final Pair<ArrayDeque<AnnotatedProgramPoint>, ArrayDeque<IIcfgTransition<?>>> newErrorPathAndTrace =
				expandSummaries(errorTrace, errorPath);

		errorPath = newErrorPathAndTrace.getFirst();
		errorTrace = newErrorPathAndTrace.getSecond();

		final IIcfgTransition<?>[] errorTraceArray = new IIcfgTransition<?>[errorTrace.size()];
		errorTrace.toArray(errorTraceArray);
		final NestedWord<IIcfgTransition<?>> errorNW =
				new NestedWord<>(errorTraceArray, computeNestingRelation(errorTraceArray));

		final AnnotatedProgramPoint[] errorPathArray = new AnnotatedProgramPoint[errorPath.size()];
		errorPath.toArray(errorPathArray);

		return new Pair<>(errorPathArray, errorNW);
	}

	private Pair<ArrayDeque<AnnotatedProgramPoint>, ArrayDeque<IIcfgTransition<?>>> expandSummaries(
			final ArrayDeque<IIcfgTransition<?>> errorTrace, final ArrayDeque<AnnotatedProgramPoint> errorPath) {
		ArrayDeque<IIcfgTransition<?>> oldErrorTrace = errorTrace;
		ArrayDeque<AnnotatedProgramPoint> oldErrorPath = errorPath;

		boolean repeat = true;

		while (repeat) {
			repeat = false;
			final ArrayDeque<IIcfgTransition<?>> newErrorTrace = new ArrayDeque<>();
			final ArrayDeque<AnnotatedProgramPoint> newErrorPath = new ArrayDeque<>();

			final Iterator<AnnotatedProgramPoint> pathIt = oldErrorPath.iterator();
			final Iterator<IIcfgTransition<?>> traceIt = oldErrorTrace.iterator();

			AnnotatedProgramPoint nextApp = pathIt.next();

			while (traceIt.hasNext()) {
				final IIcfgTransition<?> currentCodeBlock = traceIt.next();
				final AnnotatedProgramPoint previousApp = nextApp;

				newErrorPath.add(previousApp);
				newErrorTrace.add(currentCodeBlock);

				nextApp = pathIt.next();

				if (currentCodeBlock instanceof DummyCodeBlock) {
					assert mSummaryEdges.get(previousApp).contains(nextApp);

					newErrorTrace.removeLast();

					final Pair<AnnotatedProgramPoint, AnnotatedProgramPoint> sourceAndTarget =
							new Pair<>(previousApp, nextApp);

					AppDoubleDecker toInsertAdd = mSummaryEdgeToReturnSucc.get(sourceAndTarget);

					final LinkedList<IIcfgTransition<?>> traceToInsert = new LinkedList<>();
					final LinkedList<AnnotatedProgramPoint> pathToInsert = new LinkedList<>();

					while (!(toInsertAdd.mInEdge.mLabel instanceof IIcfgCallTransition<?>)) { // is this exit condition
																								// adequate? -- mb via
																								// source and target?
						if (toInsertAdd.mInEdge.mLabel instanceof DummyCodeBlock) {
							repeat = true;// this happens, we have a nested summary --> we need to expand the result
											// again
						}
						traceToInsert.add(toInsertAdd.mInEdge.mLabel);
						pathToInsert.add(toInsertAdd.mInEdge.mSource.mTop);
						toInsertAdd = toInsertAdd.mInEdge.mSource;
					}
					if (toInsertAdd.mInEdge.mLabel instanceof DummyCodeBlock) {
						repeat = true;
					}
					traceToInsert.add(toInsertAdd.mInEdge.mLabel);

					Collections.reverse(pathToInsert);
					Collections.reverse(traceToInsert);
					newErrorPath.addAll(pathToInsert);
					newErrorTrace.addAll(traceToInsert);
				}
			}
			newErrorPath.add(nextApp);

			oldErrorTrace = newErrorTrace;
			oldErrorPath = newErrorPath;
		}

		return new Pair<>(oldErrorPath, oldErrorTrace);
	}

	/**
	 * Compute the nesting relation for a given error path in the NestedWord format from Matthias. Also does a sanity
	 * check: If there is a IIcfgReturnTransition<?,?> following a IIcfgCallTransition<?> that it does not fit to, a
	 * special array is returned. This Array is of the form {special constant, first non-matching- return-index,
	 * non-matching-call index}
	 */
	private static int[] computeNestingRelation(final IIcfgTransition<?>[] errorPath) {
		final int[] nr = new int[errorPath.length];
		final Stack<IIcfgCallTransition<?>> callStack = new Stack<>();
		final Stack<Integer> callStackIndizes = new Stack<>();
		for (int i = 0; i < nr.length; i++) {
			if (errorPath[i] instanceof IIcfgCallTransition<?>) {
				nr[i] = -2;
				callStack.push((IIcfgCallTransition<?>) errorPath[i]);
				callStackIndizes.push(i);
			} else if (errorPath[i] instanceof IIcfgReturnTransition<?, ?>) {
				if (callStackIndizes.isEmpty()) {
					nr[i] = NestedWord.MINUS_INFINITY;
					break;
				}
				final IIcfgCallTransition<?> matchingCall = callStack.pop();
				if (((IIcfgReturnTransition<?, ?>) errorPath[i]).getCorrespondingCall().equals(matchingCall)) {
					nr[i] = callStackIndizes.pop();
					nr[nr[i]] = i;
				} else {
					return new int[] { BAD_NESTING_RELATION_INIT, i, callStackIndizes.pop() };
				}

			} else {
				nr[i] = NestedWord.INTERNAL_POSITION;
			}
		}
		// calls that are still on the stack are pending
		for (final Integer i : callStackIndizes) {
			nr[i] = NestedWord.PLUS_INFINITY;
		}
		return nr;
	}

	private static final class AppDoubleDecker {
		private final AnnotatedProgramPoint mTop;
		private final AnnotatedProgramPoint mBot;

		private final Stack<IIcfgCallTransition<?>> mCallStack;
		private final Stack<AnnotatedProgramPoint> mCallPredStack;
		private final ArrayList<AnnotatedProgramPoint> mPathToRoot = new ArrayList<>();

		private AddEdge mInEdge;
		private final ArrayList<AddEdge> mOutEdges = new ArrayList<>();

		AppDoubleDecker(final AnnotatedProgramPoint top, final AnnotatedProgramPoint bot,
				final Stack<IIcfgCallTransition<?>> callStack, final Stack<AnnotatedProgramPoint> callPredStack) {
			mTop = top;
			mBot = bot;
			mCallPredStack = callPredStack;
			mCallStack = callStack;
		}

		void setPathToRoot() {
			mPathToRoot.addAll(mInEdge.mSource.mPathToRoot);
			mPathToRoot.add(mTop);
		}

		@Override
		public int hashCode() {
			return HashUtils.hashJenkins(mTop.hashCode(), mBot.hashCode());
		}

		@Override
		public boolean equals(final Object add) {
			if (add instanceof AppDoubleDecker) {
				return mTop.equals(((AppDoubleDecker) add).mTop) && mBot.equals(((AppDoubleDecker) add).mBot);
			}
			return false;
		}

		@Override
		public String toString() {
			return "(" + mTop + "|" + mBot + ")";
		}
	}

	private static final class AddEdge {
		private final AppDoubleDecker mSource;
		private final AppDoubleDecker mTarget;
		private final IIcfgTransition<?> mLabel;

		public AddEdge(final AppDoubleDecker source, final AppDoubleDecker target, final IIcfgTransition<?> label) {
			super();
			assert label != null;
			mSource = source;
			mTarget = target;
			mLabel = label;
		}

		@Override
		public String toString() {
			return mSource + "--" + mLabel + "-->" + mTarget;
		}
	}

}
