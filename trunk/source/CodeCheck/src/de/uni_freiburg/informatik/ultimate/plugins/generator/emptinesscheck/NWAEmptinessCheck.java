/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.DummyStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AnnotatedProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppHyperEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;

public class NWAEmptinessCheck implements IEmptinessCheck {
	private final IUltimateServiceProvider mServices;

	public NWAEmptinessCheck(final IUltimateServiceProvider services) {
		mServices = services;
	}

	@Override
	public NestedRun<CodeBlock, AnnotatedProgramPoint> checkForEmptiness(final AnnotatedProgramPoint root) {
		final INestedWordAutomatonSimple<CodeBlock, AnnotatedProgramPoint> converted = new MyNWA(root);
		try {
			return new IsEmpty<CodeBlock, AnnotatedProgramPoint>(new AutomataLibraryServices(mServices),
					(new RemoveUnreachable<CodeBlock, AnnotatedProgramPoint>(new AutomataLibraryServices(mServices), converted)).getResult()).getNestedRun();
		} catch (final AutomataOperationCanceledException e) {
			e.printStackTrace();
			return null;
		}
	}

	class MyNWA implements INestedWordAutomatonSimple<CodeBlock, AnnotatedProgramPoint> {

		private final Set<CodeBlock> _alphabet = new HashSet<CodeBlock>();
		private final Set<CodeBlock> _internalAlphabet = new HashSet<CodeBlock>();
		private final Set<CodeBlock> _callAlphabet = new HashSet<CodeBlock>();
		private final Set<CodeBlock> _returnAlphabet = new HashSet<CodeBlock>();

		private final IStateFactory<AnnotatedProgramPoint> _stateFactory = new DummyStateFactory<AnnotatedProgramPoint>();

		private final Map<AnnotatedProgramPoint, HashSet<CodeBlock>> _stateToLettersInternal = new HashMap<AnnotatedProgramPoint, HashSet<CodeBlock>>();
		private final Map<AnnotatedProgramPoint, HashSet<CodeBlock>> _stateToLettersCall = new HashMap<AnnotatedProgramPoint, HashSet<CodeBlock>>();
		private final Map<AnnotatedProgramPoint, HashSet<CodeBlock>> _stateToLettersReturn = new HashMap<AnnotatedProgramPoint, HashSet<CodeBlock>>();

		private final Map<AnnotatedProgramPoint, HashMap<CodeBlock, ArrayList<OutgoingInternalTransition<CodeBlock, AnnotatedProgramPoint>>>> _stateToLetterToOutgoingInternalTransitions = new HashMap<AnnotatedProgramPoint, HashMap<CodeBlock, ArrayList<OutgoingInternalTransition<CodeBlock, AnnotatedProgramPoint>>>>();
		private final Map<AnnotatedProgramPoint, HashMap<CodeBlock, ArrayList<OutgoingCallTransition<CodeBlock, AnnotatedProgramPoint>>>> _stateToLetterToOutgoingCallTransitions = new HashMap<AnnotatedProgramPoint, HashMap<CodeBlock, ArrayList<OutgoingCallTransition<CodeBlock, AnnotatedProgramPoint>>>>();
		private final Map<AnnotatedProgramPoint, HashMap<AnnotatedProgramPoint, HashMap<CodeBlock, ArrayList<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>>>>> _stateToHierToLetterToOutgoingReturnTransitions = new HashMap<AnnotatedProgramPoint, HashMap<AnnotatedProgramPoint, HashMap<CodeBlock, ArrayList<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>>>>>();

		private final AnnotatedProgramPoint _emptyStackSymbol = new EmptyStackSymbol();
		private final List<AnnotatedProgramPoint> _initialStates;
		private int _size = 0;

		/**
		 * create an NWA from a AnnotatedProgramPoint-graph given its root
		 */
		public MyNWA(final AnnotatedProgramPoint root) {
			_initialStates = Collections.singletonList(root);
			exploreGraph(root);
		}

		void exploreGraph(final AnnotatedProgramPoint root) {
			final HashSet<AnnotatedProgramPoint> visitedNodes = new HashSet<AnnotatedProgramPoint>();
			// HashSet<CodeBlock> visitedEdges = new HashSet<CodeBlock>();
			final ArrayDeque<AnnotatedProgramPoint> openNodes = new ArrayDeque<AnnotatedProgramPoint>();

			openNodes.add(root);

			while (!openNodes.isEmpty()) {
				final AnnotatedProgramPoint currentNode = openNodes.pollFirst();
				assert !visitedNodes.contains(currentNode);
				visitedNodes.add(currentNode);
				assert visitedNodes.contains(currentNode);

				// for (int i = 0; i < currentNode.getOutgoingNodes().size();
				// i++) {
				// AnnotatedProgramPoint targetNode =
				// currentNode.getOutgoingNodes().get(i);
				// CodeBlock edge = currentNode.getOutgoingEdgeLabels().get(i);
				for (final AppEdge outEdge : currentNode.getOutgoingEdges()) {
					final AnnotatedProgramPoint targetNode = outEdge.getTarget();
					final CodeBlock statement = outEdge.getStatement();

					if (!visitedNodes.contains(targetNode) && !openNodes.contains(targetNode)) {
						// openNodes.contains:
																								// not
																								// nice
																								// (linear)
																								// -->
																								// do
																								// it
																								// different
						openNodes.add(targetNode);
					}

					_size++;

					if (statement instanceof Call) {
						_callAlphabet.add(statement);

						if (_stateToLettersCall.get(currentNode) == null) {
							_stateToLettersCall.put(currentNode, new HashSet<CodeBlock>());
						}
						_stateToLettersCall.get(currentNode).add(statement);

						if (_stateToLetterToOutgoingCallTransitions.get(currentNode) == null) {
							_stateToLetterToOutgoingCallTransitions
									.put(currentNode,
											new HashMap<CodeBlock, ArrayList<OutgoingCallTransition<CodeBlock, AnnotatedProgramPoint>>>());
						}
						if (_stateToLetterToOutgoingCallTransitions.get(currentNode).get(statement) == null) {
							_stateToLetterToOutgoingCallTransitions.get(currentNode).put(statement,
									new ArrayList<OutgoingCallTransition<CodeBlock, AnnotatedProgramPoint>>());
						}
						_stateToLetterToOutgoingCallTransitions
								.get(currentNode)
								.get(statement)
								.add(new OutgoingCallTransition<CodeBlock, AnnotatedProgramPoint>(statement, targetNode));

					} else if (statement instanceof Return) {
						_returnAlphabet.add(statement);

						if (_stateToLettersReturn.get(currentNode) == null) {
							_stateToLettersReturn.put(currentNode, new HashSet<CodeBlock>());
						}
						_stateToLettersReturn.get(currentNode).add(statement);

						final AppHyperEdge outHyperEdge = (AppHyperEdge) outEdge;

						final AnnotatedProgramPoint hier = outHyperEdge.getHier();
						// currentNode.getOutgoingReturnCallPreds().get(i);
						assert hier != null;

						if (_stateToHierToLetterToOutgoingReturnTransitions.get(currentNode) == null) {
							_stateToHierToLetterToOutgoingReturnTransitions
									.put(currentNode,
											new HashMap<AnnotatedProgramPoint, HashMap<CodeBlock, ArrayList<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>>>>());
						}
						if (_stateToHierToLetterToOutgoingReturnTransitions.get(currentNode).get(hier) == null) {
							_stateToHierToLetterToOutgoingReturnTransitions
									.get(currentNode)
									.put(hier,
											new HashMap<CodeBlock, ArrayList<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>>>());
						}
						if (_stateToHierToLetterToOutgoingReturnTransitions.get(currentNode).get(hier).get(statement) == null) {
							_stateToHierToLetterToOutgoingReturnTransitions
									.get(currentNode)
									.get(hier)
									.put(statement,
											new ArrayList<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>>());
						}
						assert isOutReturnTransitionNotContained(currentNode, hier, statement, targetNode);
						_stateToHierToLetterToOutgoingReturnTransitions
								.get(currentNode)
								.get(hier)
								.get(statement)
								.add(new OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>(hier, statement,
										targetNode));

						// HashSet<AnnotatedProgramPoint> hiers =
						// currentNode.getCallPredsOfOutgoingReturnTarget(targetNode);
						//
						// for (AnnotatedProgramPoint hier : hiers) {
						// if
						// (_stateToHierToLetterToOutgoingReturnTransitions.get(currentNode)
						// == null)
						// _stateToHierToLetterToOutgoingReturnTransitions.put(currentNode,
						// new HashMap<AnnotatedProgramPoint, HashMap<CodeBlock,
						// ArrayList<OutgoingReturnTransition<CodeBlock,AnnotatedProgramPoint>>>>());
						// if
						// (_stateToHierToLetterToOutgoingReturnTransitions.get(currentNode).get(hier)
						// == null)
						// _stateToHierToLetterToOutgoingReturnTransitions.get(currentNode).put(hier,
						// new HashMap<CodeBlock,
						// ArrayList<OutgoingReturnTransition<CodeBlock,AnnotatedProgramPoint>>>());
						// if
						// (_stateToHierToLetterToOutgoingReturnTransitions.get(currentNode).get(hier).get(edge)
						// == null)
						// _stateToHierToLetterToOutgoingReturnTransitions.get(currentNode).get(hier).put(edge,
						// new
						// ArrayList<OutgoingReturnTransition<CodeBlock,AnnotatedProgramPoint>>());
						// _stateToHierToLetterToOutgoingReturnTransitions.get(currentNode).get(hier).get(edge)
						// .add(new OutgoingReturnTransition<CodeBlock,
						// AnnotatedProgramPoint>(hier, edge, targetNode));
						// }
					} else {
						_internalAlphabet.add(statement);

						if (_stateToLettersInternal.get(currentNode) == null) {
							_stateToLettersInternal.put(currentNode, new HashSet<CodeBlock>());
						}
						_stateToLettersInternal.get(currentNode).add(statement);

						if (_stateToLetterToOutgoingInternalTransitions.get(currentNode) == null) {
							_stateToLetterToOutgoingInternalTransitions
									.put(currentNode,
											new HashMap<CodeBlock, ArrayList<OutgoingInternalTransition<CodeBlock, AnnotatedProgramPoint>>>());
						}
						if (_stateToLetterToOutgoingInternalTransitions.get(currentNode).get(statement) == null) {
							_stateToLetterToOutgoingInternalTransitions.get(currentNode).put(statement,
									new ArrayList<OutgoingInternalTransition<CodeBlock, AnnotatedProgramPoint>>());
						}
						_stateToLetterToOutgoingInternalTransitions
								.get(currentNode)
								.get(statement)
								.add(new OutgoingInternalTransition<CodeBlock, AnnotatedProgramPoint>(statement,
										targetNode));
					}

				}
			}

			_alphabet.addAll(_callAlphabet);
			_alphabet.addAll(_returnAlphabet);
			_alphabet.addAll(_internalAlphabet);
		}

		private boolean isOutReturnTransitionNotContained(final AnnotatedProgramPoint currentNode,
				final AnnotatedProgramPoint hier, final CodeBlock edge, final AnnotatedProgramPoint targetNode) {
			boolean result = true;
			for (final OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint> ort : _stateToHierToLetterToOutgoingReturnTransitions
					.get(currentNode).get(hier).get(edge)) {
				result &= ort.getHierPred() != hier || ort.getLetter() != edge || ort.getSucc() != targetNode;
			}
			return result;
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
		public IStateFactory<AnnotatedProgramPoint> getStateFactory() {
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
		public boolean isInitial(final AnnotatedProgramPoint state) {
			return _initialStates.contains(state);
		}

		@Override
		public boolean isFinal(final AnnotatedProgramPoint state) {
			return state.isErrorLocation();
		}

		@Override
		public Set<CodeBlock> lettersInternal(final AnnotatedProgramPoint state) {
			final HashMap<CodeBlock, ArrayList<OutgoingInternalTransition<CodeBlock, AnnotatedProgramPoint>>> letter2 = _stateToLetterToOutgoingInternalTransitions
					.get(state);
			if (letter2 == null) {
				return Collections.emptySet();
			}

			return letter2.keySet();
		}

		@Override
		public Set<CodeBlock> lettersCall(final AnnotatedProgramPoint state) {
			final HashMap<CodeBlock, ArrayList<OutgoingCallTransition<CodeBlock, AnnotatedProgramPoint>>> letter2 = _stateToLetterToOutgoingCallTransitions
					.get(state);
			if (letter2 == null) {
				return Collections.emptySet();
			}

			return _stateToLetterToOutgoingCallTransitions.get(state).keySet();
		}

		@Override
		public Set<CodeBlock> lettersReturn(final AnnotatedProgramPoint state) {
			final HashMap<AnnotatedProgramPoint, HashMap<CodeBlock, ArrayList<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>>>> hier2 = _stateToHierToLetterToOutgoingReturnTransitions
					.get(state);
			if (hier2 == null) {
				return Collections.emptySet();
			}

			final HashSet<CodeBlock> hs = new HashSet<CodeBlock>();
			for (final HashMap<CodeBlock, ArrayList<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>>> hm : hier2
					.values()) {
				hs.addAll(hm.keySet());
			}
			return hs;
		}

		@Override
		public Iterable<OutgoingInternalTransition<CodeBlock, AnnotatedProgramPoint>> internalSuccessors(
				final AnnotatedProgramPoint state, final CodeBlock letter) {
			final HashMap<CodeBlock, ArrayList<OutgoingInternalTransition<CodeBlock, AnnotatedProgramPoint>>> letter2 = _stateToLetterToOutgoingInternalTransitions
					.get(state);
			if (letter2 == null) {
				return Collections.emptyList();
			}

			return letter2.get(letter);
		}

		@Override
		public Iterable<OutgoingInternalTransition<CodeBlock, AnnotatedProgramPoint>> internalSuccessors(
				final AnnotatedProgramPoint state) {
			final HashMap<CodeBlock, ArrayList<OutgoingInternalTransition<CodeBlock, AnnotatedProgramPoint>>> letter2 = _stateToLetterToOutgoingInternalTransitions
					.get(state);
			if (letter2 == null) {
				return Collections.emptyList();
			}

			final ArrayList<OutgoingInternalTransition<CodeBlock, AnnotatedProgramPoint>> a = new ArrayList<OutgoingInternalTransition<CodeBlock, AnnotatedProgramPoint>>();
			for (final ArrayList<OutgoingInternalTransition<CodeBlock, AnnotatedProgramPoint>> vs : letter2.values()) {
				a.addAll(vs);
			}
			return a;
		}

		@Override
		public Iterable<OutgoingCallTransition<CodeBlock, AnnotatedProgramPoint>> callSuccessors(
				final AnnotatedProgramPoint state, final CodeBlock letter) {
			final HashMap<CodeBlock, ArrayList<OutgoingCallTransition<CodeBlock, AnnotatedProgramPoint>>> letter2 = _stateToLetterToOutgoingCallTransitions
					.get(state);
			if (letter2 == null) {
				return Collections.emptyList();
			}

			return _stateToLetterToOutgoingCallTransitions.get(state).get(letter);
		}

		@Override
		public Iterable<OutgoingCallTransition<CodeBlock, AnnotatedProgramPoint>> callSuccessors(
				final AnnotatedProgramPoint state) {
			final HashMap<CodeBlock, ArrayList<OutgoingCallTransition<CodeBlock, AnnotatedProgramPoint>>> letter2 = _stateToLetterToOutgoingCallTransitions
					.get(state);
			if (letter2 == null) {
				return Collections.emptyList();
			}

			final ArrayList<OutgoingCallTransition<CodeBlock, AnnotatedProgramPoint>> a = new ArrayList<OutgoingCallTransition<CodeBlock, AnnotatedProgramPoint>>();
			for (final ArrayList<OutgoingCallTransition<CodeBlock, AnnotatedProgramPoint>> vs : _stateToLetterToOutgoingCallTransitions
					.get(state).values()) {
				a.addAll(vs);
			}
			return a;
		}

		@Override
		public Iterable<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>> returnSuccessors(
				final AnnotatedProgramPoint state, final AnnotatedProgramPoint hier, final CodeBlock letter) {
			final HashMap<AnnotatedProgramPoint, HashMap<CodeBlock, ArrayList<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>>>> hier2letter2 = _stateToHierToLetterToOutgoingReturnTransitions
					.get(state);
			if (hier2letter2 == null) {
				return Collections.emptyList();
			}
			final HashMap<CodeBlock, ArrayList<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>>> letter2 = _stateToHierToLetterToOutgoingReturnTransitions
					.get(state).get(hier);
			if (letter2 == null) {
				return Collections.emptyList();
			}

			return _stateToHierToLetterToOutgoingReturnTransitions.get(state).get(hier).get(letter);
		}

		@Override
		public Iterable<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>> returnSuccessorsGivenHier(
				final AnnotatedProgramPoint state, final AnnotatedProgramPoint hier) {
			final HashMap<AnnotatedProgramPoint, HashMap<CodeBlock, ArrayList<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>>>> hier2letter2 = _stateToHierToLetterToOutgoingReturnTransitions
					.get(state);
			if (hier2letter2 == null) {
				return Collections.emptyList();
			}
			final HashMap<CodeBlock, ArrayList<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>>> letter2 = _stateToHierToLetterToOutgoingReturnTransitions
					.get(state).get(hier);
			if (letter2 == null) {
				return Collections.emptyList();
			}

			final ArrayList<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>> a = new ArrayList<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>>();
			for (final ArrayList<OutgoingReturnTransition<CodeBlock, AnnotatedProgramPoint>> vs : _stateToHierToLetterToOutgoingReturnTransitions
					.get(state).get(hier).values()) {
				a.addAll(vs);
			}
			return a;
		}

	}

	class EmptyStackSymbol extends AnnotatedProgramPoint {

		private static final long serialVersionUID = 1L;

		public EmptyStackSymbol() {
			super((IPredicate) null, (BoogieIcfgLocation) null);
		}

		@Override
		public boolean equals(final Object o) {
			return o instanceof EmptyStackSymbol;
		}

		@Override
		public String toString() {
			return "E";
		}
	}
}
