package de.uni_freiburg.informatik.ultimate.plugins.generator.impulse;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;

public class EmptinessCheck {
	private static int c_badNestingRelationInit = -7;
	
	HashMap<AnnotatedProgramPoint, ArrayList<AnnotatedProgramPoint>> callPredecessorToItsCallPredecessors;
	ArrayDeque<AppDoubleDecker> openNodes;
	HashSet<AppDoubleDecker> visitedNodes;
	HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>> summaryEdges;
	
	/**
	 * Search for a nested error path within the graph with the given root. Return null
	 * if there is none.
	 * @param root
	 * @return
	 */
	Pair<AnnotatedProgramPoint[],NestedWord<CodeBlock>> checkForEmptiness(AnnotatedProgramPoint root) {
		callPredecessorToItsCallPredecessors = 	
				new HashMap<AnnotatedProgramPoint, ArrayList<AnnotatedProgramPoint>>();
		openNodes = new ArrayDeque<EmptinessCheck.AppDoubleDecker>();
		visitedNodes = new HashSet<EmptinessCheck.AppDoubleDecker>();
		
		summaryEdges = 
				new HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>>();
		
		EmptyStackSymbol emptyStackSymbol = new EmptyStackSymbol(null, null);
		
		openNodes.add(new AppDoubleDecker(root, emptyStackSymbol));
		Pair<AnnotatedProgramPoint[],NestedWord<CodeBlock>> returnedPath = null;
		
		while (!openNodes.isEmpty() && returnedPath == null) {
			AppDoubleDecker currentAdd = openNodes.pollFirst();
			visitedNodes.add(currentAdd);
						
			for (AnnotatedProgramPoint app : currentAdd.top.getOutgoingNodes()) {
				CodeBlock edge = currentAdd.top.getOutgoingEdgeLabel(app);
				
				AppDoubleDecker newAdd = null;
				
				if (!(edge instanceof Call || edge instanceof Return)) {

					newAdd = new AppDoubleDecker(app, currentAdd.bot);
					returnedPath = openNewNode(currentAdd, app, edge, newAdd);
					
				} else if (edge instanceof Call) {

					newAdd = new AppDoubleDecker(app, currentAdd.top);
					updateCallPredecessorMapping(currentAdd.top, currentAdd.bot);
					returnedPath = openNewNode(currentAdd, app, edge, newAdd);
				
				} else if (edge instanceof Return) {
					ArrayList<AnnotatedProgramPoint> cps = callPredecessorToItsCallPredecessors.get(currentAdd.bot);
					
					//only take return edges that match the current callpredecessor
//					if (!((Return) edge).getCallerNode().equals(currentAdd.bot.getProgramPoint()))
					if (!currentAdd.top.outGoingReturnAppToCallPredContains(app, currentAdd.bot))
						continue;
						
					//the question is: which are the callpredecessors for the new doubledecker
					// this is stored in the hashmap
					for (AnnotatedProgramPoint callPredPred : cps) {
						newAdd = new AppDoubleDecker(app, callPredPred);
						addSummaryEdge(currentAdd.bot, app);
						if (returnedPath == null)//TODO: diese Abfrage auch an den anderen Stellen?
							returnedPath = openNewNode(currentAdd, app, edge, newAdd);
					}
				}
			}
			
			//also unwind summaryEdges
			for (AnnotatedProgramPoint target : summaryEdges.get(currentAdd.top)) {
				AppDoubleDecker	newAdd = new AppDoubleDecker(target, currentAdd.bot);
				returnedPath = openNewNode(currentAdd, target, null, newAdd);//convention: AddEdges which are summaries are labeled "null"
			}
			
		}
		return returnedPath;
	}


	private void addSummaryEdge(AnnotatedProgramPoint bot,
			AnnotatedProgramPoint app) {
		HashSet<AnnotatedProgramPoint> targets = summaryEdges.get(bot);
		if (targets == null)
			targets = new HashSet<AnnotatedProgramPoint>();
		targets.add(app);
		summaryEdges.put(bot, targets);
	}


	private Pair<AnnotatedProgramPoint[],NestedWord<CodeBlock>> openNewNode(
			AppDoubleDecker currentAdd, AnnotatedProgramPoint app,
			CodeBlock edge, AppDoubleDecker newAdd) {
		if (!visitedNodes.contains(newAdd)){
			newAdd.appendToPath(new AddEdge(currentAdd, newAdd, edge));

			if (app.isErrorLocation())
				return reconstructPath(newAdd);

			openNodes.add(newAdd);

//			if (!(edge instanceof Call || edge instanceof Return)) {
//
//
//			} else if (edge instanceof Call) {
//
//			} else if (edge instanceof Return) {
//
//			}
		}
		return null;
	}
	
	
	private void updateCallPredecessorMapping(AnnotatedProgramPoint top,
			AnnotatedProgramPoint bot) {
		ArrayList<AnnotatedProgramPoint> cps = callPredecessorToItsCallPredecessors.get(top);
		if (cps == null) {
			cps = new ArrayList<AnnotatedProgramPoint>();
		} 
		cps.add(bot);
		callPredecessorToItsCallPredecessors.put(top, cps);
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
		
		CodeBlock[] errorTraceArray = new CodeBlock[errorTrace.size()];
		errorTrace.toArray(errorTraceArray);
		NestedWord<CodeBlock> errorNW = new NestedWord<CodeBlock>(
				errorTraceArray, computeNestingRelation(errorTraceArray));
		
		AnnotatedProgramPoint[] errorPathArray = new AnnotatedProgramPoint[errorPath.size()];
		errorPath.toArray(errorPathArray);
		
		expandSummaries(errorTrace, errorPath);
		
		return new Pair<AnnotatedProgramPoint[], NestedWord<CodeBlock>>(errorPathArray, errorNW);
	}

	private void expandSummaries(ArrayDeque<CodeBlock> errorTrace,
			ArrayDeque<AnnotatedProgramPoint> errorPath) {
		
	}


	/**
	 * Compute the nesting relation for a given error path in the NestedWord format from Matthias.
	 * Also does a sanity check: If there is a Return following a Call that it does not fit to, a
	 * special array is returned. This Array is of the form {special constant, first non-matching-
	 * return-index, non-matching-call index}
	 */
	private static int[] computeNestingRelation(CodeBlock[] errorPath) {
		int [] nr = new int[errorPath.length];
		Stack<Call> callStack = new Stack<Call>();
		Stack<Integer> callStackIndizes = new Stack<Integer>();
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
				Call matchingCall = callStack.pop();
				if (((Return) errorPath[i]).getCorrespondingCallAnnot().equals(matchingCall)) {
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
		for (Integer i : callStackIndizes)
			nr[i] = NestedWord.PLUS_INFINITY;
		return nr;
	}

	class AppDoubleDecker {
		AnnotatedProgramPoint top;
		AnnotatedProgramPoint bot;
		
		AddEdge inEdge;
		ArrayList<AddEdge> outEdges = new ArrayList<AddEdge>();
		
		ArrayList<AddEdge> path = new ArrayList<AddEdge>();
		
		AppDoubleDecker(AnnotatedProgramPoint top, AnnotatedProgramPoint bot) {
			this.top = top;
			this.bot = bot;
		}
		
		boolean equals(AppDoubleDecker add) {
			return this.top.equals(add.top) && this.bot.equals(add.bot);
		}
		
		void appendToPath(AddEdge edge) {
			path.add(edge);
		}
	}
	
	class AddEdge {
		AppDoubleDecker source;
		AppDoubleDecker target;
		CodeBlock label;
		
		public AddEdge(AppDoubleDecker source, AppDoubleDecker target,
				CodeBlock label) {
			super();
			this.source = source;
			this.target = target;
			this.label = label;
		}
	}
	
	class EmptyStackSymbol extends AnnotatedProgramPoint {
		
		private static final long serialVersionUID = 1L;

		public EmptyStackSymbol(IPredicate predicate, ProgramPoint programPoint) {
			super(null, null);
		}
		
		boolean equals(EmptyStackSymbol ess) {
			return true;
		}
	}

}
