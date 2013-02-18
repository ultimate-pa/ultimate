package de.uni_freiburg.informatik.ultimate.plugins.generator.impulse;

import java.util.ArrayDeque;
import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

public class ErrorPathBuilder {
	
	public Pair<AnnotatedProgramPoint[], NestedWord<CodeBlock>> getErrorPathAsNestedWord(IEdge procedureEdge) {
		Pair<AnnotatedProgramPoint[], CodeBlock[]> errorPath = bfsSearch(procedureEdge);
		
		if (errorPath == null) {
			return null;
		}
		int[] nestingRelation = computeNestingRelation(errorPath.getSecond());
		
		NestedWord<CodeBlock> errorPathAsNestedWord = 
				new NestedWord<CodeBlock>(errorPath.getSecond(), nestingRelation); 
		
		return new Pair<AnnotatedProgramPoint[], NestedWord<CodeBlock>>(
				errorPath.getFirst(), errorPathAsNestedWord);
	}
	
	private static int[] computeNestingRelation(CodeBlock[] errorPath) {
		int [] nr = new int[errorPath.length];
		ArrayDeque<Integer> callStack = new ArrayDeque<Integer>();
		for (int i = 0; i < nr.length; i++) {
			if (errorPath[i] instanceof Call) {
				nr[i] = -2;
				callStack.push(i);
			} else if (errorPath[i] instanceof Return) {
				nr[i] = callStack.pop();
				nr[nr[i]] = i;
			} else {
				nr[i] = -2;
			}
		}
		return nr;
	}

	private Pair<AnnotatedProgramPoint[], CodeBlock[]> bfsSearch(IEdge rootEdge) {
		ArrayDeque<BFSState> openBFSStates =  new ArrayDeque<BFSState>();
		BFSState initialBFSState = new BFSState(rootEdge.getTarget(), rootEdge,
				null, rootEdge, new ArrayList<BFSState>());
		openBFSStates.add(initialBFSState);
		
		while(!openBFSStates.isEmpty()) {
			BFSState currentBFSState = openBFSStates.pollFirst();
			AnnotatedProgramPoint currentProgramPoint =
					(AnnotatedProgramPoint) currentBFSState.getBFSState();
			ArrayList<BFSState> currentPathPrefix = currentBFSState.getPathPrefix();
			BFSState currentCallPoint = currentBFSState.getCallState();
			IEdge currentCall = currentBFSState.getCall();
			for (INode node : currentProgramPoint.getOutgoingNodes()) {
				AnnotatedProgramPoint newProgramPoint = (AnnotatedProgramPoint) node;
				CodeBlock edge = currentProgramPoint.getOutgoingCodeBlockOf(newProgramPoint);
				BFSState newCallPoint = currentCallPoint;
				if(edge instanceof Return && currentCallPoint != null) {
					newCallPoint = currentCallPoint.getCallState();
				}
				if (hasBeenExpanded(currentPathPrefix,
						newProgramPoint, newCallPoint)) {
					continue;
				}
				IEdge newCall = currentCall;
				ArrayList<BFSState> newPathPrefix = new ArrayList<BFSState>();
				newPathPrefix.addAll(currentPathPrefix);
				newPathPrefix.add(currentBFSState);
				if (edge instanceof Call) {
					newCall = (Call) edge;
					newCallPoint = currentBFSState;
				} else if (edge instanceof Return) {
					Return redge = (Return) edge;
					Call caller = redge.getCorrespondingCallAnnot();
					if(caller.equals(currentCall)) {
						newCall = currentCallPoint.getCall();
						newCallPoint = currentCallPoint.getCallState();
					} else {
						continue;
					}
				} else if (edge instanceof Summary) {
					continue;
				}
				BFSState newBFSState = new BFSState(newProgramPoint, edge,
						newCallPoint, newCall, newPathPrefix);
				if (newProgramPoint.isErrorLocation()) {
					newPathPrefix.add(newBFSState);
					return getPath(newPathPrefix);
				}
				openBFSStates.add(newBFSState);
			}
		}
		return null;
	}
	
	private boolean hasBeenExpanded(ArrayList<BFSState> path,
			INode programPoint, BFSState callPoint) {
		BFSState dummyState = new BFSState(programPoint,
				null, callPoint, null, null);
		for (int i = path.size()-1; i >= 0; i--) {
			BFSState state = path.get(i);
			if (state.equals(dummyState)) {
				return true;
			}
		}
		return false;
	}
	
	private Pair<AnnotatedProgramPoint[], CodeBlock[]> getPath(ArrayList<BFSState> bfsStatePath) {
		ArrayList<CodeBlock> codeblocks = new ArrayList<CodeBlock>();
		ArrayList<AnnotatedProgramPoint> annoPoints = new ArrayList<AnnotatedProgramPoint>();
		for (int i = 0; i < bfsStatePath.size(); i++) {
			BFSState bfsState = bfsStatePath.get(i);
			if (bfsState.getTakenEdge() instanceof CodeBlock) {
				codeblocks.add((CodeBlock)bfsState.getTakenEdge());
				annoPoints.add((AnnotatedProgramPoint) bfsState.getBFSState());
			}
		}
		AnnotatedProgramPoint[] result1 =
				new AnnotatedProgramPoint[annoPoints.size()];
		CodeBlock[] result2 = new CodeBlock[codeblocks.size()];
		
		return new Pair<AnnotatedProgramPoint[], CodeBlock[]>(
				annoPoints.toArray(result1),codeblocks.toArray(result2));
	}	
	
//	static class NestedWordBuilder {
//		
//		NestedWordBuilder(AbstractEdgeNode rootNode) {
//			
//		}
//	}
	
	class BFSState {
		private BFSState m_callState;
		private IEdge m_call;
		private IEdge m_takenEdge;
		private INode m_AnnotatedProgamPoint;
		private ArrayList<BFSState> m_pathPrefix;
		
		public BFSState(INode annotatedProgramPoint, IEdge takenEdge, BFSState callState,
				IEdge call, ArrayList<BFSState> pathPrefix) {
			m_callState = callState;
			m_call = call;
			m_takenEdge = takenEdge;
			m_AnnotatedProgamPoint = annotatedProgramPoint;
			m_pathPrefix = pathPrefix;
		}
		
		public BFSState getCallState() {
			return m_callState;
		}
		
		public IEdge getCall() {
			return m_call;
		}
		
		public INode getBFSState() {
			return m_AnnotatedProgamPoint;
		}
		
		public IEdge getTakenEdge() {
			return m_takenEdge;
		}
		
		public ArrayList<BFSState> getPathPrefix() {
			return m_pathPrefix;
		}
		
		public boolean equals(BFSState other) {
			if (other == null)
					return false;

			boolean callPointsAreEqual = false;
			
			BFSState otherCallState = other.getCallState();
			INode otherCallPoint = otherCallState == null ? null : otherCallState.getBFSState();
			INode callPoint = m_callState == null ? null : m_callState.getBFSState();
			
			if (callPoint == null)
				if (otherCallPoint == null)
					callPointsAreEqual = true;
				else 
					callPointsAreEqual = false;
			else
				callPointsAreEqual = callPoint.equals(otherCallPoint);
			
			
			return (callPointsAreEqual &&
					m_AnnotatedProgamPoint.equals(other.getBFSState()));
		}
		
		public String toString() {
			String output = "";
			if (m_takenEdge instanceof CodeBlock) {
				output += ((CodeBlock)m_takenEdge).getPrettyPrintedStatements();
			} else {
				output += m_takenEdge.toString(); 
			}
			output += " " + m_AnnotatedProgamPoint.toString();
			return output;
			
		}
	}
}
