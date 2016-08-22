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
package de.uni_freiburg.informatik.ultimate.plugins.generator.emptinesscheck;

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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AnnotatedProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.DummyCodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class BFSEmptinessCheck implements IEmptinessCheck {
	private static int c_badNestingRelationInit = -7;

	ArrayDeque<AppDoubleDecker> openNodes;
	HashSet<AppDoubleDecker> visitedNodes;
	HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>> summaryEdges;
	HashMap<Pair<AnnotatedProgramPoint,AnnotatedProgramPoint>, AppDoubleDecker> summaryEdgeToReturnSucc;

	private final ILogger mLogger;

	
	public BFSEmptinessCheck(ILogger logger){
		mLogger = logger;
	}
	
	/**
	 * Search for a nested error path within the graph with the given root. Return null
	 * if there is none.
	 * @param root
	 * @return
	 */
	@Override
	public NestedRun<CodeBlock, AnnotatedProgramPoint> checkForEmptiness(AnnotatedProgramPoint root) {
		openNodes = new ArrayDeque<BFSEmptinessCheck.AppDoubleDecker>();
		visitedNodes = new HashSet<BFSEmptinessCheck.AppDoubleDecker>();

		summaryEdges = 
				new HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>>();
		summaryEdgeToReturnSucc =
				new HashMap<Pair<AnnotatedProgramPoint,AnnotatedProgramPoint>, AppDoubleDecker>();

		final EmptyStackSymbol emptyStackSymbol = new EmptyStackSymbol();

		openNodes.add(new AppDoubleDecker(root, emptyStackSymbol, 
				new Stack<Call>(), new Stack<AnnotatedProgramPoint>()));
		Pair<AnnotatedProgramPoint[],NestedWord<CodeBlock>> returnedPath = null;

		while (!openNodes.isEmpty() && returnedPath == null) {
			final AppDoubleDecker currentAdd = openNodes.pollFirst();
			visitedNodes.add(currentAdd);

			for (final AnnotatedProgramPoint app : currentAdd.top.getOutgoingNodes()) {
//				CodeBlock edge = currentAdd.top.getOutgoingEdgeLabel(app); //FIXME
				final CodeBlock edge = null;

				if (edge instanceof Summary) {
					continue;
				}

				AppDoubleDecker newAdd = null;

				if (!(edge instanceof Call || edge instanceof Return)) {

					newAdd = new AppDoubleDecker(app, currentAdd.bot,
							(Stack<Call>) currentAdd.callStack.clone(),
							(Stack<AnnotatedProgramPoint>) currentAdd.callPredStack.clone());
					if (returnedPath == null) {
						returnedPath = openNewNode(currentAdd, app, edge, newAdd);
					}

				} else if (edge instanceof Call) {

					newAdd = new AppDoubleDecker(app, currentAdd.top, 
							(Stack<Call>) currentAdd.callStack.clone(),
							(Stack<AnnotatedProgramPoint>) currentAdd.callPredStack.clone());
					newAdd.callStack.add((Call) edge);
					newAdd.callPredStack.add(currentAdd.bot);

					if (returnedPath == null) {
						returnedPath = openNewNode(currentAdd, app, edge, newAdd);
					}

				} else if (edge instanceof Return) {
					//only take return edges that return to the current callpredecessor
					//					if (!((Return) edge).getCallerNode().equals(currentAdd.bot.getProgramPoint()))
//					if (currentAdd.top.getOutgoingReturnCallPreds().get(currentAdd.top.getOutgoingNodes().indexOf(app)) != currentAdd.bot) //FIXME
////							old: "!currentAdd.top.outGoingReturnAppToCallPredContains(app, currentAdd.bot))"
//						continue;

					final Stack<Call> currentCallStack = (Stack<Call>) currentAdd.callStack.clone();
					final Stack<AnnotatedProgramPoint> currentCpStack = (Stack<AnnotatedProgramPoint>) currentAdd.callPredStack.clone();

					final Call poppedCall = currentCallStack.pop();
					final AnnotatedProgramPoint callPredPred = currentCpStack.pop();

					if (!((Return) edge).getCorrespondingCall().equals(poppedCall)) {
						continue;
					}

					newAdd = new AppDoubleDecker(app, callPredPred, currentCallStack, currentCpStack);

					addSummaryEdge(currentAdd.bot, app);
					final Pair<AnnotatedProgramPoint, AnnotatedProgramPoint> pairToAdd = 
							new Pair<AnnotatedProgramPoint, AnnotatedProgramPoint>(currentAdd.bot, app); //rausgezogen fuer debugging
					summaryEdgeToReturnSucc.put(pairToAdd, newAdd);
//					System.out.println("--------------- " + pairToAdd + " --> " + pairToAdd.hashCode());
					if (returnedPath == null) {
						returnedPath = openNewNode(currentAdd, app, edge, newAdd);
					}
				}
			}

			//also unwind summaryEdges
			final HashSet<AnnotatedProgramPoint> targets = summaryEdges.get(currentAdd.top);
			if (targets != null) {
				for (final AnnotatedProgramPoint target : targets) {
					final AppDoubleDecker	newAdd = new AppDoubleDecker(
							target, currentAdd.bot, 
							(Stack<Call>) currentAdd.callStack.clone(),
							(Stack<AnnotatedProgramPoint>) currentAdd.callPredStack.clone());
					if (returnedPath == null)
					 {
						returnedPath = openNewNode(currentAdd, target, new DummyCodeBlock(mLogger), newAdd);//convention: AddEdges which are summaries are labeled "null"
					}
				}
			}
		}
		return returnedPath == null ? 
				null :
			new NestedRun<CodeBlock, AnnotatedProgramPoint>(returnedPath.getSecond(), 
				new ArrayList<AnnotatedProgramPoint>(Arrays.asList(returnedPath.getFirst())));
	}


	private void addSummaryEdge(AnnotatedProgramPoint bot,
			AnnotatedProgramPoint app) {
		HashSet<AnnotatedProgramPoint> targets = summaryEdges.get(bot);
		if (targets == null) {
			targets = new HashSet<AnnotatedProgramPoint>();
		}
		targets.add(app);
		summaryEdges.put(bot, targets);
	}


	private Pair<AnnotatedProgramPoint[],NestedWord<CodeBlock>> openNewNode(
			AppDoubleDecker currentAdd, AnnotatedProgramPoint app,
			CodeBlock edge, AppDoubleDecker newAdd) {
		if (!visitedNodes.contains(newAdd)){
			final AddEdge newAddEdge = new AddEdge(currentAdd, newAdd, edge);
			newAdd.inEdge = newAddEdge;
			currentAdd.outEdges.add(newAddEdge);
			newAdd.setPathToRoot();

			if (app.isErrorLocation()) {
				return reconstructPath(newAdd);
			}

			openNodes.add(newAdd);
		}
		return null;
	}

	private Pair<AnnotatedProgramPoint[], NestedWord<CodeBlock>> reconstructPath(
			AppDoubleDecker errorAdd) {
		ArrayDeque<AnnotatedProgramPoint> errorPath = new ArrayDeque<AnnotatedProgramPoint>();
		ArrayDeque<CodeBlock> errorTrace = new ArrayDeque<CodeBlock>();

		AppDoubleDecker currentAdd = errorAdd;
		AddEdge currentInEdge = errorAdd.inEdge;

		while (currentInEdge != null) {
			errorPath.addFirst(currentAdd.top);
			errorTrace.addFirst(currentInEdge.label);

			currentAdd = currentInEdge.source;
			currentInEdge = currentAdd.inEdge;
		}
		errorPath.addFirst(currentAdd.top);

		final Pair<ArrayDeque<AnnotatedProgramPoint>, ArrayDeque<CodeBlock>> newErrorPathAndTrace = 
				expandSummaries(errorTrace, errorPath);

		errorPath = newErrorPathAndTrace.getFirst();
		errorTrace = newErrorPathAndTrace.getSecond();

		final CodeBlock[] errorTraceArray = new CodeBlock[errorTrace.size()];
		errorTrace.toArray(errorTraceArray);
		final NestedWord<CodeBlock> errorNW = new NestedWord<CodeBlock>(
				errorTraceArray, computeNestingRelation(errorTraceArray));

		final AnnotatedProgramPoint[] errorPathArray = new AnnotatedProgramPoint[errorPath.size()];
		errorPath.toArray(errorPathArray);

		return new Pair<AnnotatedProgramPoint[], NestedWord<CodeBlock>>(errorPathArray, errorNW);
	}

	private Pair<ArrayDeque<AnnotatedProgramPoint>, ArrayDeque<CodeBlock>> expandSummaries(ArrayDeque<CodeBlock> errorTrace,
			ArrayDeque<AnnotatedProgramPoint> errorPath) {
		ArrayDeque<CodeBlock> oldErrorTrace = errorTrace;
		ArrayDeque<AnnotatedProgramPoint> oldErrorPath = errorPath;

		boolean repeat = true;

		while (repeat) {
			repeat = false;
			final ArrayDeque<CodeBlock> newErrorTrace = new ArrayDeque<CodeBlock>();
			final ArrayDeque<AnnotatedProgramPoint> newErrorPath = new ArrayDeque<AnnotatedProgramPoint>();

			final Iterator<AnnotatedProgramPoint> pathIt = oldErrorPath.iterator();
			final Iterator<CodeBlock> traceIt = oldErrorTrace.iterator();

			AnnotatedProgramPoint nextApp = pathIt.next();			

			while (traceIt.hasNext()) {
				final CodeBlock currentCodeBlock = traceIt.next();
				final AnnotatedProgramPoint previousApp = nextApp;

				newErrorPath.add(previousApp);
				newErrorTrace.add(currentCodeBlock);

				nextApp = pathIt.next();

				if (currentCodeBlock instanceof DummyCodeBlock) {
					assert summaryEdges.get(previousApp).contains(nextApp);
					
					newErrorTrace.removeLast();

					final Pair<AnnotatedProgramPoint, AnnotatedProgramPoint> sourceAndTarget = 
							new Pair<AnnotatedProgramPoint, AnnotatedProgramPoint>(previousApp, nextApp);

					AppDoubleDecker toInsertAdd = summaryEdgeToReturnSucc.get(sourceAndTarget);

					final LinkedList<CodeBlock> traceToInsert = new LinkedList<CodeBlock>();
					final LinkedList<AnnotatedProgramPoint> pathToInsert = new LinkedList<AnnotatedProgramPoint>();

					while (!(toInsertAdd.inEdge.label instanceof Call)) { //is this exit condition adequate? -- mb via source and target? 
						if (toInsertAdd.inEdge.label instanceof DummyCodeBlock)
						 {
							repeat = true;// this happens, we have a nested summary --> we need to expand the result again 
						}
						traceToInsert.add(toInsertAdd.inEdge.label);
						pathToInsert.add(toInsertAdd.inEdge.source.top);
						toInsertAdd = toInsertAdd.inEdge.source;
					}
					if (toInsertAdd.inEdge.label instanceof DummyCodeBlock) {
						repeat = true;
					}
					traceToInsert.add(toInsertAdd.inEdge.label);
					
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

		return new Pair<ArrayDeque<AnnotatedProgramPoint>, ArrayDeque<CodeBlock>>(oldErrorPath, oldErrorTrace);
	}


	/**
	 * Compute the nesting relation for a given error path in the NestedWord format from Matthias.
	 * Also does a sanity check: If there is a Return following a Call that it does not fit to, a
	 * special array is returned. This Array is of the form {special constant, first non-matching-
	 * return-index, non-matching-call index}
	 */
	private static int[] computeNestingRelation(CodeBlock[] errorPath) {
		final int [] nr = new int[errorPath.length];
		final Stack<Call> callStack = new Stack<Call>();
		final Stack<Integer> callStackIndizes = new Stack<Integer>();
		for (int i = 0; i < nr.length; i++) {
			if (errorPath[i] instanceof Call) {
				nr[i] = -2;
				callStack.push((Call) errorPath[i]);
				callStackIndizes.push(i);
			} else if (errorPath[i] instanceof Return) {
				if (callStackIndizes.isEmpty()) {
					nr[i] = NestedWord.MINUS_INFINITY;
					break;
				}
				final Call matchingCall = callStack.pop();
				if (((Return) errorPath[i]).getCorrespondingCall().equals(matchingCall)) {
					nr[i] = callStackIndizes.pop();
					nr[nr[i]] = i;	
				} else {
					return new int[] {c_badNestingRelationInit , i, callStackIndizes.pop()};
				}

			} else {
				nr[i] = NestedWord.INTERNAL_POSITION;
			}
		}
		//calls that are still on the stack are pending
		for (final Integer i : callStackIndizes) {
			nr[i] = NestedWord.PLUS_INFINITY;
		}
		return nr;
	}

	class AppDoubleDecker {
		AnnotatedProgramPoint top;
		AnnotatedProgramPoint bot;

		Stack<Call> callStack;
		Stack<AnnotatedProgramPoint> callPredStack;
		ArrayList<AnnotatedProgramPoint> pathToRoot = new ArrayList<AnnotatedProgramPoint>();

		AddEdge inEdge;
		ArrayList<AddEdge> outEdges = new ArrayList<AddEdge>();

		AppDoubleDecker(AnnotatedProgramPoint top, AnnotatedProgramPoint bot, 
				Stack<Call> callStack, Stack<AnnotatedProgramPoint> callPredStack) {
			this.top = top;
			this.bot = bot;
			this.callPredStack = callPredStack;
			this.callStack = callStack;
		}

		//added for debugging purposes
		void setPathToRoot() {
			pathToRoot.addAll(inEdge.source.pathToRoot);
			pathToRoot.add(top);
			//			if (pathToRoot.size() > 2)
			//				reconstructPath(this);
		}

		@Override
		public int hashCode() {
			return HashUtils.hashJenkins(top.hashCode(), bot.hashCode());
		}

		@Override
		public boolean equals(Object add) {
			if (add instanceof AppDoubleDecker) {
				return top.equals(((AppDoubleDecker)add).top) && 
						bot.equals(((AppDoubleDecker)add).bot);
			} else {
				return false;
			}
		}

		@Override
		public String toString() {
			return "(" + top + "|" + bot + ")";
		}
	}

	class AddEdge {
		AppDoubleDecker source;
		AppDoubleDecker target;
		CodeBlock label;

		public AddEdge(AppDoubleDecker source, AppDoubleDecker target,
				CodeBlock label) {
			super();
			assert (label != null);
			this.source = source;
			this.target = target;
			this.label = label;
		}

		@Override
		public String toString() {
			return source + "--" + label + "-->" + target;
		}
	}

	class EmptyStackSymbol extends AnnotatedProgramPoint {

		private static final long serialVersionUID = 1L;

		public EmptyStackSymbol() {
			super((IPredicate) null, (ProgramPoint) null);
		}

		@Override
		public boolean equals(Object o) {
			if (o instanceof EmptyStackSymbol) {
				return true;
			} else {
				return false;
			}
		}

		@Override
		public String toString() {
			return "E";
		}
	}

}
