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
package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.emptinesscheck;

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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.DummyStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AnnotatedProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppHyperEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.EmptyStackSymbol;

public class NWAEmptinessCheck implements IEmptinessCheck {
	private final IUltimateServiceProvider mServices;

	public NWAEmptinessCheck(final IUltimateServiceProvider services) {
		mServices = services;
	}

	@Override
	public NestedRun<IIcfgTransition<?>, AnnotatedProgramPoint> checkForEmptiness(final AnnotatedProgramPoint root) {
		final INwaOutgoingLetterAndTransitionProvider<IIcfgTransition<?>, AnnotatedProgramPoint> converted =
				new MyNWA(root);
		try {
			return new IsEmpty<>(new AutomataLibraryServices(mServices),
					new RemoveUnreachable<>(new AutomataLibraryServices(mServices), converted).getResult())
							.getNestedRun();
		} catch (final AutomataOperationCanceledException e) {
			throw new ToolchainCanceledException(e,
					new RunningTaskInfo(NWAEmptinessCheck.class, "checking for new error trace"));
		}
	}

	private static final class MyNWA
			implements INwaOutgoingLetterAndTransitionProvider<IIcfgTransition<?>, AnnotatedProgramPoint> {

		private final Set<IIcfgTransition<?>> mAlphabet = new HashSet<>();
		private final Set<IIcfgTransition<?>> mInternalAlphabet = new HashSet<>();
		private final Set<IIcfgTransition<?>> mCallAlphabet = new HashSet<>();
		private final Set<IIcfgTransition<?>> mReturnAlphabet = new HashSet<>();
		private final VpAlphabet<IIcfgTransition<?>> mVpAlphabet =
				new VpAlphabet<>(mInternalAlphabet, mCallAlphabet, mReturnAlphabet);

		private final IStateFactory<AnnotatedProgramPoint> mStateFactory = new DummyStateFactory<>();

		private final Map<AnnotatedProgramPoint, Set<IIcfgTransition<?>>> mStateToLettersInternal = new HashMap<>();
		private final Map<AnnotatedProgramPoint, Set<IIcfgTransition<?>>> mStateToLettersCall = new HashMap<>();
		private final Map<AnnotatedProgramPoint, Set<IIcfgTransition<?>>> mStateToLettersReturn = new HashMap<>();

		private final Map<AnnotatedProgramPoint, Map<IIcfgTransition<?>, List<OutgoingInternalTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>>> mStateToLetterToOutgoingInternalTransitions =
				new HashMap<>();
		private final Map<AnnotatedProgramPoint, Map<IIcfgTransition<?>, List<OutgoingCallTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>>> mStateToLetterToOutgoingCallTransitions =
				new HashMap<>();
		private final Map<AnnotatedProgramPoint, Map<AnnotatedProgramPoint, Map<IIcfgTransition<?>, List<OutgoingReturnTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>>>> mStateToHierToLetterToOutgoingReturnTransitions =
				new HashMap<>();

		private final AnnotatedProgramPoint mEmptyStackSymbol = new EmptyStackSymbol();
		private final List<AnnotatedProgramPoint> mInitialStates;
		private int mSize = 0;

		/**
		 * create an NWA from a AnnotatedProgramPoint-graph given its root
		 */
		public MyNWA(final AnnotatedProgramPoint root) {
			mInitialStates = Collections.singletonList(root);
			exploreGraph(root);
		}

		void exploreGraph(final AnnotatedProgramPoint root) {
			final HashSet<AnnotatedProgramPoint> visitedNodes = new HashSet<>();
			final ArrayDeque<AnnotatedProgramPoint> openNodes = new ArrayDeque<>();

			openNodes.add(root);

			while (!openNodes.isEmpty()) {
				final AnnotatedProgramPoint currentNode = openNodes.pollFirst();
				assert !visitedNodes.contains(currentNode);
				visitedNodes.add(currentNode);
				assert visitedNodes.contains(currentNode);

				for (final AppEdge outEdge : currentNode.getOutgoingEdges()) {
					final AnnotatedProgramPoint targetNode = outEdge.getTarget();
					final IIcfgTransition<?> statement = outEdge.getStatement();

					if (!visitedNodes.contains(targetNode) && !openNodes.contains(targetNode)) {
						// TODO: openNodes.contains: not nice (linear)-->do it different
						openNodes.add(targetNode);
					}

					mSize++;

					if (statement instanceof IIcfgCallTransition<?>) {
						mCallAlphabet.add(statement);

						if (mStateToLettersCall.get(currentNode) == null) {
							mStateToLettersCall.put(currentNode, new HashSet<IIcfgTransition<?>>());
						}
						mStateToLettersCall.get(currentNode).add(statement);

						if (mStateToLetterToOutgoingCallTransitions.get(currentNode) == null) {
							mStateToLetterToOutgoingCallTransitions.put(currentNode,
									new HashMap<IIcfgTransition<?>, List<OutgoingCallTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>>());
						}
						if (mStateToLetterToOutgoingCallTransitions.get(currentNode).get(statement) == null) {
							mStateToLetterToOutgoingCallTransitions.get(currentNode).put(statement,
									new ArrayList<OutgoingCallTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>());
						}
						mStateToLetterToOutgoingCallTransitions.get(currentNode).get(statement)
								.add(new OutgoingCallTransition<>(statement, targetNode));

					} else if (statement instanceof IIcfgReturnTransition<?, ?>) {
						mReturnAlphabet.add(statement);

						if (mStateToLettersReturn.get(currentNode) == null) {
							mStateToLettersReturn.put(currentNode, new HashSet<IIcfgTransition<?>>());
						}
						mStateToLettersReturn.get(currentNode).add(statement);

						final AppHyperEdge outHyperEdge = (AppHyperEdge) outEdge;

						final AnnotatedProgramPoint hier = outHyperEdge.getHier();
						assert hier != null;

						if (mStateToHierToLetterToOutgoingReturnTransitions.get(currentNode) == null) {
							mStateToHierToLetterToOutgoingReturnTransitions.put(currentNode,
									new HashMap<AnnotatedProgramPoint, Map<IIcfgTransition<?>, List<OutgoingReturnTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>>>());
						}
						if (mStateToHierToLetterToOutgoingReturnTransitions.get(currentNode).get(hier) == null) {
							mStateToHierToLetterToOutgoingReturnTransitions.get(currentNode).put(hier,
									new HashMap<IIcfgTransition<?>, List<OutgoingReturnTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>>());
						}
						if (mStateToHierToLetterToOutgoingReturnTransitions.get(currentNode).get(hier)
								.get(statement) == null) {
							mStateToHierToLetterToOutgoingReturnTransitions.get(currentNode).get(hier).put(statement,
									new ArrayList<OutgoingReturnTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>());
						}
						assert isOutReturnTransitionNotContained(currentNode, hier, statement, targetNode);
						mStateToHierToLetterToOutgoingReturnTransitions.get(currentNode).get(hier).get(statement)
								.add(new OutgoingReturnTransition<>(hier, statement, targetNode));
					} else {
						mInternalAlphabet.add(statement);

						if (mStateToLettersInternal.get(currentNode) == null) {
							mStateToLettersInternal.put(currentNode, new HashSet<IIcfgTransition<?>>());
						}
						mStateToLettersInternal.get(currentNode).add(statement);

						if (mStateToLetterToOutgoingInternalTransitions.get(currentNode) == null) {
							mStateToLetterToOutgoingInternalTransitions.put(currentNode,
									new HashMap<IIcfgTransition<?>, List<OutgoingInternalTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>>());
						}
						if (mStateToLetterToOutgoingInternalTransitions.get(currentNode).get(statement) == null) {
							mStateToLetterToOutgoingInternalTransitions.get(currentNode).put(statement,
									new ArrayList<OutgoingInternalTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>());
						}
						mStateToLetterToOutgoingInternalTransitions.get(currentNode).get(statement)
								.add(new OutgoingInternalTransition<>(statement, targetNode));
					}

				}
			}

			mAlphabet.addAll(mCallAlphabet);
			mAlphabet.addAll(mReturnAlphabet);
			mAlphabet.addAll(mInternalAlphabet);
		}

		private boolean isOutReturnTransitionNotContained(final AnnotatedProgramPoint currentNode,
				final AnnotatedProgramPoint hier, final IIcfgTransition<?> edge,
				final AnnotatedProgramPoint targetNode) {
			boolean result = true;
			for (final OutgoingReturnTransition<IIcfgTransition<?>, AnnotatedProgramPoint> ort : mStateToHierToLetterToOutgoingReturnTransitions
					.get(currentNode).get(hier).get(edge)) {
				result &= ort.getHierPred() != hier || ort.getLetter() != edge || ort.getSucc() != targetNode;
			}
			return result;
		}

		@Override
		public int size() {
			return mSize;
		}

		@Override
		public Set<IIcfgTransition<?>> getAlphabet() {
			return mAlphabet;
		}

		@Override
		public String sizeInformation() {
			return "no size info available";
		}

		@Override
		public VpAlphabet<IIcfgTransition<?>> getVpAlphabet() {
			return mVpAlphabet;
		}

		@Override
		public IStateFactory<AnnotatedProgramPoint> getStateFactory() {
			return mStateFactory;
		}

		@Override
		public AnnotatedProgramPoint getEmptyStackState() {
			return mEmptyStackSymbol;
		}

		@Override
		public Iterable<AnnotatedProgramPoint> getInitialStates() {
			return mInitialStates;
		}

		@Override
		public boolean isInitial(final AnnotatedProgramPoint state) {
			return mInitialStates.contains(state);
		}

		@Override
		public boolean isFinal(final AnnotatedProgramPoint state) {
			return state.isErrorLocation();
		}

		@Override
		public Set<IIcfgTransition<?>> lettersInternal(final AnnotatedProgramPoint state) {
			final Map<IIcfgTransition<?>, List<OutgoingInternalTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>> letter2 =
					mStateToLetterToOutgoingInternalTransitions.get(state);
			if (letter2 == null) {
				return Collections.emptySet();
			}

			return letter2.keySet();
		}

		@Override
		public Set<IIcfgTransition<?>> lettersCall(final AnnotatedProgramPoint state) {
			final Map<IIcfgTransition<?>, List<OutgoingCallTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>> letter2 =
					mStateToLetterToOutgoingCallTransitions.get(state);
			if (letter2 == null) {
				return Collections.emptySet();
			}

			return mStateToLetterToOutgoingCallTransitions.get(state).keySet();
		}

		@Override
		public Set<IIcfgTransition<?>> lettersReturn(final AnnotatedProgramPoint state,
				final AnnotatedProgramPoint hier) {
			final Map<AnnotatedProgramPoint, Map<IIcfgTransition<?>, List<OutgoingReturnTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>>> hier2 =
					mStateToHierToLetterToOutgoingReturnTransitions.get(state);
			if (hier2 == null) {
				return Collections.emptySet();
			}
			final Map<IIcfgTransition<?>, List<OutgoingReturnTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>> letter2succ =
					hier2.get(hier2);
			return letter2succ.keySet();
		}

		@Override
		public Iterable<OutgoingInternalTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>
				internalSuccessors(final AnnotatedProgramPoint state, final IIcfgTransition<?> letter) {
			final Map<IIcfgTransition<?>, List<OutgoingInternalTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>> letter2 =
					mStateToLetterToOutgoingInternalTransitions.get(state);
			if (letter2 == null) {
				return Collections.emptyList();
			}

			return letter2.get(letter);
		}

		@Override
		public Iterable<OutgoingInternalTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>
				internalSuccessors(final AnnotatedProgramPoint state) {
			final Map<IIcfgTransition<?>, List<OutgoingInternalTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>> letter2 =
					mStateToLetterToOutgoingInternalTransitions.get(state);
			if (letter2 == null) {
				return Collections.emptyList();
			}

			final ArrayList<OutgoingInternalTransition<IIcfgTransition<?>, AnnotatedProgramPoint>> a =
					new ArrayList<>();
			for (final List<OutgoingInternalTransition<IIcfgTransition<?>, AnnotatedProgramPoint>> vs : letter2
					.values()) {
				a.addAll(vs);
			}
			return a;
		}

		@Override
		public Iterable<OutgoingCallTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>
				callSuccessors(final AnnotatedProgramPoint state, final IIcfgTransition<?> letter) {
			final Map<IIcfgTransition<?>, List<OutgoingCallTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>> letter2 =
					mStateToLetterToOutgoingCallTransitions.get(state);
			if (letter2 == null) {
				return Collections.emptyList();
			}

			return mStateToLetterToOutgoingCallTransitions.get(state).get(letter);
		}

		@Override
		public Iterable<OutgoingCallTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>
				callSuccessors(final AnnotatedProgramPoint state) {
			final Map<IIcfgTransition<?>, List<OutgoingCallTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>> letter2 =
					mStateToLetterToOutgoingCallTransitions.get(state);
			if (letter2 == null) {
				return Collections.emptyList();
			}

			final ArrayList<OutgoingCallTransition<IIcfgTransition<?>, AnnotatedProgramPoint>> a = new ArrayList<>();
			for (final List<OutgoingCallTransition<IIcfgTransition<?>, AnnotatedProgramPoint>> vs : mStateToLetterToOutgoingCallTransitions
					.get(state).values()) {
				a.addAll(vs);
			}
			return a;
		}

		@Override
		public Iterable<OutgoingReturnTransition<IIcfgTransition<?>, AnnotatedProgramPoint>> returnSuccessors(
				final AnnotatedProgramPoint state, final AnnotatedProgramPoint hier, final IIcfgTransition<?> letter) {
			final Map<AnnotatedProgramPoint, Map<IIcfgTransition<?>, List<OutgoingReturnTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>>> hier2letter2 =
					mStateToHierToLetterToOutgoingReturnTransitions.get(state);
			if (hier2letter2 == null) {
				return Collections.emptyList();
			}
			final Map<IIcfgTransition<?>, List<OutgoingReturnTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>> letter2 =
					mStateToHierToLetterToOutgoingReturnTransitions.get(state).get(hier);
			if (letter2 == null) {
				return Collections.emptyList();
			}

			return mStateToHierToLetterToOutgoingReturnTransitions.get(state).get(hier).get(letter);
		}

		@Override
		public Iterable<OutgoingReturnTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>
				returnSuccessorsGivenHier(final AnnotatedProgramPoint state, final AnnotatedProgramPoint hier) {
			final Map<AnnotatedProgramPoint, Map<IIcfgTransition<?>, List<OutgoingReturnTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>>> hier2letter2 =
					mStateToHierToLetterToOutgoingReturnTransitions.get(state);
			if (hier2letter2 == null) {
				return Collections.emptyList();
			}
			final Map<IIcfgTransition<?>, List<OutgoingReturnTransition<IIcfgTransition<?>, AnnotatedProgramPoint>>> letter2 =
					mStateToHierToLetterToOutgoingReturnTransitions.get(state).get(hier);
			if (letter2 == null) {
				return Collections.emptyList();
			}

			final ArrayList<OutgoingReturnTransition<IIcfgTransition<?>, AnnotatedProgramPoint>> a = new ArrayList<>();
			for (final List<OutgoingReturnTransition<IIcfgTransition<?>, AnnotatedProgramPoint>> vs : mStateToHierToLetterToOutgoingReturnTransitions
					.get(state).get(hier).values()) {
				a.addAll(vs);
			}
			return a;
		}

		@Override
		public IElement transformToUltimateModel(final AutomataLibraryServices services)
				throws AutomataOperationCanceledException {
			// TODO Auto-generated method stub
			return null;
		}

	}
}
