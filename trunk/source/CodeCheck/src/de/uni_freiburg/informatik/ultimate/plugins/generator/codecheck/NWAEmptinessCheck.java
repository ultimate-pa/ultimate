package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;

public class NWAEmptinessCheck implements IEmptinessCheck {

	@Override
	public NestedRun<CodeBlock, AnnotatedProgramPoint> checkForEmptiness(
			AnnotatedProgramPoint root) {
		INestedWordAutomatonSimple<CodeBlock, AnnotatedProgramPoint> converted = new MyNWA(root);
		try {
			return new IsEmpty<CodeBlock, AnnotatedProgramPoint>(
					(new RemoveUnreachable<CodeBlock, AnnotatedProgramPoint>(converted)).getResult()).getNestedRun();
		} catch (OperationCanceledException e) {
			e.printStackTrace();
			return null;
		}
	}

	class MyNWA implements INestedWordAutomatonSimple<CodeBlock, AnnotatedProgramPoint> {
		
		private Set<CodeBlock> _alphabet = new HashSet<CodeBlock>();
		private Set<CodeBlock> _internalAlphabet = new HashSet<CodeBlock>();
		private Set<CodeBlock> _callAlphabet = new HashSet<CodeBlock>();
		private Set<CodeBlock> _returnAlphabet = new HashSet<CodeBlock>();

		private StateFactory<AnnotatedProgramPoint> _stateFactory =
				new MyStateFactory<AnnotatedProgramPoint>();
		
		private Map<AnnotatedProgramPoint, HashSet<CodeBlock>> _stateToLettersInternal =
				new HashMap<AnnotatedProgramPoint, HashSet<CodeBlock>>(); 
		private Map<AnnotatedProgramPoint, HashSet<CodeBlock>> _stateToLettersCall =
				new HashMap<AnnotatedProgramPoint, HashSet<CodeBlock>>(); 
		private Map<AnnotatedProgramPoint, HashSet<CodeBlock>> _stateToLettersReturn =
				new HashMap<AnnotatedProgramPoint, HashSet<CodeBlock>>(); 
		
		private Map<AnnotatedProgramPoint,HashMap<CodeBlock,
			ArrayList<OutgoingInternalTransition<CodeBlock,AnnotatedProgramPoint>>>> 
			_stateToLetterToOutgoingInternalTransitions =
				new HashMap<AnnotatedProgramPoint, HashMap<CodeBlock, 
				ArrayList<OutgoingInternalTransition<CodeBlock, AnnotatedProgramPoint>>>>();
		private Map<AnnotatedProgramPoint,HashMap<CodeBlock,
			ArrayList<OutgoingCallTransition<CodeBlock,AnnotatedProgramPoint>>>> 
			_stateToLetterToOutgoingCallTransitions =
				new HashMap<AnnotatedProgramPoint, HashMap<CodeBlock, 
				ArrayList<OutgoingCallTransition<CodeBlock, AnnotatedProgramPoint>>>>();
		private Map<AnnotatedProgramPoint,HashMap<AnnotatedProgramPoint, HashMap<CodeBlock,
			ArrayList<OutgoingReturnTransition<CodeBlock,AnnotatedProgramPoint>>>>> 
			_stateToHierToLetterToOutgoingReturnTransitions =
				new HashMap<AnnotatedProgramPoint, HashMap<AnnotatedProgramPoint, HashMap<CodeBlock,
				ArrayList<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>>>>>();
			
		
		private AnnotatedProgramPoint _emptyStackSymbol = new EmptyStackSymbol();
		private List<AnnotatedProgramPoint> _initialStates;
		private int _size = 0;

		/**
		 * create an NWA from a AnnotatedProgramPoint-graph given its root
		 */
		public MyNWA(AnnotatedProgramPoint root) {
			_initialStates = Collections.singletonList(root);
			exploreGraph(root);
		}
		
		void exploreGraph(AnnotatedProgramPoint root) {
			HashSet<AnnotatedProgramPoint> visitedNodes = new HashSet<AnnotatedProgramPoint>();
//			HashSet<CodeBlock> visitedEdges = new HashSet<CodeBlock>();
			ArrayDeque<AnnotatedProgramPoint> openNodes = new ArrayDeque<AnnotatedProgramPoint>();
			
			openNodes.add(root);
			
			while (!openNodes.isEmpty()) {
				AnnotatedProgramPoint currentNode = openNodes.pollFirst();
				visitedNodes.add(currentNode);
				
				for (int i = 0; i < currentNode.getOutgoingNodes().size(); i++) {
					AnnotatedProgramPoint targetNode = currentNode.getOutgoingNodes().get(i);
					if (!visitedNodes.contains(targetNode))
						openNodes.add(targetNode);
					
					CodeBlock edge = currentNode.getOutgoingEdgeLabels().get(i);
					
					_size++;
					
					if (edge instanceof Call) {
						_callAlphabet.add(edge);
						
						if (_stateToLettersCall.get(currentNode) == null)
							_stateToLettersCall.put(currentNode, new HashSet<CodeBlock>());
						_stateToLettersCall.get(currentNode).add(edge);
						
						if (_stateToLetterToOutgoingCallTransitions.get(currentNode) == null)
							_stateToLetterToOutgoingCallTransitions.put(currentNode, 
									new HashMap<CodeBlock, ArrayList<OutgoingCallTransition<CodeBlock,AnnotatedProgramPoint>>>());
						if (_stateToLetterToOutgoingCallTransitions.get(currentNode).get(edge) == null)
							_stateToLetterToOutgoingCallTransitions.get(currentNode).put(edge, 
									new ArrayList<OutgoingCallTransition<CodeBlock,AnnotatedProgramPoint>>());
						_stateToLetterToOutgoingCallTransitions.get(currentNode).get(edge)
							.add(new OutgoingCallTransition<CodeBlock, AnnotatedProgramPoint>(edge, targetNode));
						
					} else if (edge instanceof Return) {
						_returnAlphabet.add(edge);
						
						if (_stateToLettersReturn.get(currentNode) == null)
							_stateToLettersReturn.put(currentNode, new HashSet<CodeBlock>());
						_stateToLettersReturn.get(currentNode).add(edge);
						
						HashSet<AnnotatedProgramPoint> hiers = currentNode.getCallPredsOfOutgoingReturnTarget(targetNode);

						for (AnnotatedProgramPoint hier : hiers) {
							if (_stateToHierToLetterToOutgoingReturnTransitions.get(currentNode) == null)
								_stateToHierToLetterToOutgoingReturnTransitions.put(currentNode, 
										new HashMap<AnnotatedProgramPoint, HashMap<CodeBlock, 
										ArrayList<OutgoingReturnTransition<CodeBlock,AnnotatedProgramPoint>>>>());
							if (_stateToHierToLetterToOutgoingReturnTransitions.get(currentNode).get(hier) == null)
								_stateToHierToLetterToOutgoingReturnTransitions.get(currentNode).put(hier, 
										new HashMap<CodeBlock, ArrayList<OutgoingReturnTransition<CodeBlock,AnnotatedProgramPoint>>>());
							if (_stateToHierToLetterToOutgoingReturnTransitions.get(currentNode).get(hier).get(edge) == null)
								_stateToHierToLetterToOutgoingReturnTransitions.get(currentNode).get(hier).put(edge, 
										new ArrayList<OutgoingReturnTransition<CodeBlock,AnnotatedProgramPoint>>());
							_stateToHierToLetterToOutgoingReturnTransitions.get(currentNode).get(hier).get(edge)
								.add(new OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>(hier, edge, targetNode));
						}
					} else {
						_internalAlphabet.add(edge);
						
						if (_stateToLettersInternal.get(currentNode) == null)
						_stateToLettersInternal.put(currentNode, new HashSet<CodeBlock>());
						_stateToLettersInternal.get(currentNode).add(edge);
						
						if (_stateToLetterToOutgoingInternalTransitions.get(currentNode) == null)
							_stateToLetterToOutgoingInternalTransitions.put(currentNode, 
									new HashMap<CodeBlock, ArrayList<OutgoingInternalTransition<CodeBlock,AnnotatedProgramPoint>>>());
						if (_stateToLetterToOutgoingInternalTransitions.get(currentNode).get(edge) == null)
							_stateToLetterToOutgoingInternalTransitions.get(currentNode).put(edge, 
									new ArrayList<OutgoingInternalTransition<CodeBlock,AnnotatedProgramPoint>>());
						_stateToLetterToOutgoingInternalTransitions.get(currentNode).get(edge)
							.add(new OutgoingInternalTransition<CodeBlock, AnnotatedProgramPoint>(edge, targetNode));
					}
							
				}
			}
			
			_alphabet.addAll(_callAlphabet);
			_alphabet.addAll(_returnAlphabet);
			_alphabet.addAll(_internalAlphabet);
		}

		@Override
		public boolean accepts(Word<CodeBlock> word) {
			assert false;
			return false;
		}

		@Override
		public int size() {
			assert false;
			return _size;
		}

		@Override
		public Set<CodeBlock> getAlphabet() {
			return _alphabet;
		}

		@Override
		public String sizeInformation() {
			return "no size info available";
		}

		@Override
		public Set<CodeBlock> getInternalAlphabet() {
			return _internalAlphabet;
		}

		@Override
		public Set<CodeBlock> getCallAlphabet() {
			return _callAlphabet;
		}

		@Override
		public Set<CodeBlock> getReturnAlphabet() {
			return _returnAlphabet;
		}

		@Override
		public StateFactory<AnnotatedProgramPoint> getStateFactory() {
			return _stateFactory;
		}

		@Override
		public AnnotatedProgramPoint getEmptyStackState() {
			return _emptyStackSymbol;
		}

		@Override
		public Iterable<AnnotatedProgramPoint> getInitialStates() {
			return _initialStates;
		}

		@Override
		public boolean isInitial(AnnotatedProgramPoint state) {
			return _initialStates.contains(state);
		}

		@Override
		public boolean isFinal(AnnotatedProgramPoint state) {
			return state.isErrorLocation();
		}

		@Override
		public Set<CodeBlock> lettersInternal(AnnotatedProgramPoint state) {
			HashMap<CodeBlock, ArrayList<OutgoingInternalTransition<CodeBlock, AnnotatedProgramPoint>>> letter2 = 
					_stateToLetterToOutgoingInternalTransitions.get(state);
			if (letter2 == null)
				return Collections.emptySet();
			
			return letter2.keySet();
		}

		@Override
		public Set<CodeBlock> lettersCall(AnnotatedProgramPoint state) {
			HashMap<CodeBlock, ArrayList<OutgoingCallTransition<CodeBlock, AnnotatedProgramPoint>>> letter2 = 
					_stateToLetterToOutgoingCallTransitions.get(state);
			if (letter2 == null)
				return Collections.emptySet();
			
			return _stateToLetterToOutgoingCallTransitions.get(state).keySet();
		}

		@Override
		public Set<CodeBlock> lettersReturn(AnnotatedProgramPoint state) {
			HashMap<AnnotatedProgramPoint, HashMap<CodeBlock, ArrayList<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>>>> hier2 = 
					_stateToHierToLetterToOutgoingReturnTransitions.get(state);
			if (hier2 == null)
				return Collections.emptySet();
			
			HashSet<CodeBlock> hs = new HashSet<CodeBlock>();
			for (HashMap<CodeBlock, ArrayList<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>>>  hm : 
				hier2.values())
				hs.addAll(hm.keySet());
			return hs;
		}

		@Override
		public Iterable<OutgoingInternalTransition<CodeBlock, AnnotatedProgramPoint>> internalSuccessors(
				AnnotatedProgramPoint state, CodeBlock letter) {
			HashMap<CodeBlock, ArrayList<OutgoingInternalTransition<CodeBlock, AnnotatedProgramPoint>>> letter2 = 
					_stateToLetterToOutgoingInternalTransitions.get(state);
			if (letter2 == null)
				return Collections.emptyList();
			
			return letter2.get(letter);
		}

		@Override
		public Iterable<OutgoingInternalTransition<CodeBlock, AnnotatedProgramPoint>> internalSuccessors(
				AnnotatedProgramPoint state) {
			HashMap<CodeBlock, ArrayList<OutgoingInternalTransition<CodeBlock, AnnotatedProgramPoint>>> letter2 = 
					_stateToLetterToOutgoingInternalTransitions.get(state);
			if (letter2 == null)
				return Collections.emptyList();
			
			ArrayList<OutgoingInternalTransition<CodeBlock, AnnotatedProgramPoint>> a = 
					new ArrayList<OutgoingInternalTransition<CodeBlock,AnnotatedProgramPoint>>();
			for ( ArrayList<OutgoingInternalTransition<CodeBlock, AnnotatedProgramPoint>>  vs 
					: letter2.values())
				a.addAll(vs);
			return a;
		}

		@Override
		public Iterable<OutgoingCallTransition<CodeBlock, AnnotatedProgramPoint>> callSuccessors(
				AnnotatedProgramPoint state, CodeBlock letter) {
			HashMap<CodeBlock, ArrayList<OutgoingCallTransition<CodeBlock, AnnotatedProgramPoint>>> letter2 = 
					_stateToLetterToOutgoingCallTransitions.get(state);
			if (letter2 == null)
				return Collections.emptyList();
			
			return _stateToLetterToOutgoingCallTransitions.get(state).get(letter);
		}

		@Override
		public Iterable<OutgoingCallTransition<CodeBlock, AnnotatedProgramPoint>> callSuccessors(
				AnnotatedProgramPoint state) {
			HashMap<CodeBlock, ArrayList<OutgoingCallTransition<CodeBlock, AnnotatedProgramPoint>>> letter2 = 
					_stateToLetterToOutgoingCallTransitions.get(state);
			if (letter2 == null)
				return Collections.emptyList();
			
			ArrayList<OutgoingCallTransition<CodeBlock, AnnotatedProgramPoint>> a = 
					new ArrayList<OutgoingCallTransition<CodeBlock,AnnotatedProgramPoint>>();
			for ( ArrayList<OutgoingCallTransition<CodeBlock, AnnotatedProgramPoint>>  vs 
					: _stateToLetterToOutgoingCallTransitions.get(state).values())
				a.addAll(vs);
			return a;
		}

		@Override
		public Iterable<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>> returnSucccessors(
				AnnotatedProgramPoint state, AnnotatedProgramPoint hier,
				CodeBlock letter) {
			HashMap<AnnotatedProgramPoint,HashMap<CodeBlock,ArrayList<OutgoingReturnTransition<CodeBlock,AnnotatedProgramPoint>>>> hier2letter2 = 
					_stateToHierToLetterToOutgoingReturnTransitions.get(state);
			if (hier2letter2 == null)
				return Collections.emptyList();
			HashMap<CodeBlock, ArrayList<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>>> letter2 = 
					_stateToHierToLetterToOutgoingReturnTransitions.get(state).get(hier);
			if (letter2 == null)
				return Collections.emptyList();
			
			return _stateToHierToLetterToOutgoingReturnTransitions.get(state).get(hier).get(letter);
		}

		@Override
		public Iterable<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>> returnSuccessorsGivenHier(
				AnnotatedProgramPoint state, AnnotatedProgramPoint hier) {
			HashMap<AnnotatedProgramPoint,HashMap<CodeBlock,ArrayList<OutgoingReturnTransition<CodeBlock,AnnotatedProgramPoint>>>> hier2letter2 = 
					_stateToHierToLetterToOutgoingReturnTransitions.get(state);
			if (hier2letter2 == null)
				return Collections.emptyList();
			HashMap<CodeBlock, ArrayList<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>>> letter2 = 
					_stateToHierToLetterToOutgoingReturnTransitions.get(state).get(hier);
			if (letter2 == null)
				return Collections.emptyList();
						
			ArrayList<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>> a = 
					new ArrayList<OutgoingReturnTransition<CodeBlock,AnnotatedProgramPoint>>();
			for ( ArrayList<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>>  vs 
					: _stateToHierToLetterToOutgoingReturnTransitions.get(state).get(hier).values())
				a.addAll(vs);
			return a;
		}
		
	}
	
	class MyStateFactory<STATE> extends StateFactory<STATE> {
		
	}
	
	class EmptyStackSymbol extends AnnotatedProgramPoint {

		private static final long serialVersionUID = 1L;

		public EmptyStackSymbol() {
			super((IPredicate) null, (ProgramPoint) null);
		}

		public boolean equals(Object o) {
			if (o instanceof EmptyStackSymbol)
				return true;
			else
				return false;
		}

		public String toString() {
			return "E";
		}
	}
}
