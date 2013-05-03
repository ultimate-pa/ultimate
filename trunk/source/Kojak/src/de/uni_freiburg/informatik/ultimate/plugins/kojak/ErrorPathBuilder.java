package de.uni_freiburg.informatik.ultimate.plugins.kojak;

import java.util.ArrayDeque;
import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

public class ErrorPathBuilder {

	public Pair<KojakProgramPoint[], NestedWord<CodeBlock>> getErrorPathAsNestedWord(RCFGEdge edge) {
		Pair<KojakProgramPoint[], CodeBlock[]> errorPath = bfsSearch(edge);
		
		if (errorPath == null) {
			return null;
		}
		int[] nestingRelation = computeNestingRelation(errorPath.getEntry2());
		
		NestedWord<CodeBlock> errorPathAsNestedWord = 
				new NestedWord<CodeBlock>(errorPath.getEntry2(), nestingRelation); 
		
		return new Pair<KojakProgramPoint[], NestedWord<CodeBlock>>(
				errorPath.getEntry1(), errorPathAsNestedWord);
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

	private Pair<KojakProgramPoint[], CodeBlock[]> bfsSearch(RCFGEdge edge2) {
		ArrayDeque<BFSState> openBFSStates =  new ArrayDeque<BFSState>();
		BFSState initialBFSState = new BFSState(edge2.getTarget(), edge2,
				null, edge2, new ArrayList<BFSState>());
		openBFSStates.add(initialBFSState);
		
		while(!openBFSStates.isEmpty()) {
			BFSState currentBFSState = openBFSStates.pollFirst();
			KojakProgramPoint currentKojakProgramPoint =
					(KojakProgramPoint) currentBFSState.getBFSState();
			ArrayList<BFSState> currentPathPrefix = currentBFSState.getPathPrefix();
			BFSState currentCallPoint = currentBFSState.getCallState();
			RCFGEdge currentCall = currentBFSState.getCall();
			for (RCFGEdge edge : currentKojakProgramPoint.getOutgoingEdges()) {
				KojakProgramPoint newKojakProgramPoint = (KojakProgramPoint) edge.getTarget();
				BFSState newCallPoint = currentCallPoint;
				if (hasBeenExpanded(currentPathPrefix,
						newKojakProgramPoint, newCallPoint)) {
					continue;
				}
				RCFGEdge newCall = currentCall;
				ArrayList<BFSState> newPathPrefix = new ArrayList<BFSState>();
				newPathPrefix.addAll(currentPathPrefix);
				newPathPrefix.add(currentBFSState);
				if (edge instanceof Call) {
					newCall = (Call) edge;
					newCallPoint = currentBFSState;
				} else if (edge instanceof Return) {
					Return redge = (Return) edge;
					Call caller = redge.getCorrespondingCall();
					if(caller.equals(currentCall)) {
						newCall = currentCallPoint.getCall();
						newCallPoint = currentCallPoint.getCallState();
					} else {
						continue;
					}
				} else if (edge instanceof Summary) {
					continue;
				}
				BFSState newBFSState = new BFSState(newKojakProgramPoint, edge,
						newCallPoint, newCall, newPathPrefix);
				if (newKojakProgramPoint.isErrorLocation()) {
					newPathPrefix.add(newBFSState);
					return getPath(newPathPrefix);
				}
				openBFSStates.add(newBFSState);
			}
		}
		return null;
	}
	
	private boolean hasBeenExpanded(ArrayList<BFSState> path,
			KojakProgramPoint newKojakProgramPoint, BFSState callPoint) {
		BFSState dummyState = new BFSState(newKojakProgramPoint,
				null, callPoint, null, null);
		for (int i = path.size()-1; i >= 0; i--) {
			BFSState state = path.get(i);
			if (state.equals(dummyState)) {
				return true;
			}
		}
		return false;
	}
	
	private Pair<KojakProgramPoint[], CodeBlock[]> getPath(ArrayList<BFSState> bfsStatePath) {
		ArrayList<CodeBlock> codeblocks = new ArrayList<CodeBlock>();
		ArrayList<KojakProgramPoint> annoPoints = new ArrayList<KojakProgramPoint>();
		for (int i = 0; i < bfsStatePath.size(); i++) {
			BFSState bfsState = bfsStatePath.get(i);
			if (bfsState.getTakenEdge() instanceof CodeBlock) {
				codeblocks.add((CodeBlock)bfsState.getTakenEdge());
				annoPoints.add((KojakProgramPoint) bfsState.getBFSState());
			}
		}
		KojakProgramPoint[] result1 =
				new KojakProgramPoint[annoPoints.size()];
		CodeBlock[] result2 = new CodeBlock[codeblocks.size()];
		
		return new Pair<KojakProgramPoint[], CodeBlock[]>(
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
		private RCFGEdge m_call;
		private RCFGEdge m_takenEdge;
		private RCFGNode m_AnnotatedProgamPoint;
		private ArrayList<BFSState> m_pathPrefix;
		
		public BFSState(RCFGNode iExplicitEdgesMultigraph, RCFGEdge takenEdge, BFSState callState,
				RCFGEdge call, ArrayList<BFSState> pathPrefix) {
			m_callState = callState;
			m_call = call;
			m_takenEdge = takenEdge;
			m_AnnotatedProgamPoint = iExplicitEdgesMultigraph;
			m_pathPrefix = pathPrefix;
		}
		
		public BFSState getCallState() {
			return m_callState;
		}
		
		public RCFGEdge getCall() {
			return m_call;
		}
		
		public RCFGNode getBFSState() {
			return m_AnnotatedProgamPoint;
		}
		
		public RCFGEdge getTakenEdge() {
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
			RCFGNode otherCallPoint = otherCallState == null ? null : otherCallState.getBFSState();
			RCFGNode callPoint = m_callState == null ? null : m_callState.getBFSState();
			
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
