/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IAbstractStateStorage;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector.AStar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector.IEdgeDenier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector.IHeuristic;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector.RcfgWrapper;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public abstract class BaseRcfgAbstractStateStorageProvider<STATE extends IAbstractState<STATE, CodeBlock, IBoogieVar>>
		implements IAbstractStateStorage<STATE, CodeBlock, IBoogieVar, ProgramPoint> {

	private final IAbstractStateBinaryOperator<STATE> mMergeOperator;
	private final IUltimateServiceProvider mServices;
	private final List<BaseRcfgAbstractStateStorageProvider<STATE>> mChildStores;

	public BaseRcfgAbstractStateStorageProvider(IAbstractStateBinaryOperator<STATE> mergeOperator,
			IUltimateServiceProvider services) {
		assert mergeOperator != null;
		assert services != null;
		mMergeOperator = mergeOperator;
		mServices = services;
		mChildStores = new ArrayList<>();
	}

	public Collection<STATE> getAbstractPreStates(CodeBlock transition) {
		assert transition != null;
		return getAbstractStates(transition, transition.getSource());
	}

	@Override
	public List<STATE> getAbstractPostStates(CodeBlock transition) {
		assert transition != null;
		return getAbstractStates(transition, transition.getTarget());
	}

	@Override
	public STATE getCurrentAbstractPreState(final CodeBlock transition) {
		assert transition != null;

		// @formatter:off
		// The states are stored as pair (transition, state) at a state. 
		// If 
		// - the transition is outgoing, state is a prestate,
		// - the transition is incoming, state is a poststate,
		// w.r.t. to the transition.
		// If we want the prestate for a given transition, we first check if for that transition a prestate is saved. 
		// If not, then we just take the last state at this node.
		// TODO: Do we have to merge all states at this location to be sound? 
		// @formatter:on

		final STATE rtr = getCurrentState(transition.getSource(), a -> transition.equals(a));
		if (rtr == null) {
			return getCurrentState(transition.getSource(), a -> true);
		}
		return rtr;

		// return getCurrentState(transition.getSource(), a -> transition.getSource().equals(a.getTarget()));
		// return getCurrentState(transition.getSource(), a -> transition.equals(a));
	}

	@Override
	public STATE getCurrentAbstractPostState(final CodeBlock transition) {
		assert transition != null;
		return getCurrentState(transition.getTarget(), a -> transition.equals(a));
	}

	@Override
	public void addAbstractPreState(CodeBlock transition, STATE state) {
		assert transition != null;
		assert state != null;
		addState(transition, state, transition.getSource());
	}

	@Override
	public void addAbstractPostState(CodeBlock transition, STATE state) {
		assert transition != null;
		assert state != null;
		addState(transition, state, transition.getTarget());
	}

	@Override
	public STATE mergePostStates(CodeBlock transition) {
		assert transition != null;
		final Deque<Pair<CodeBlock, STATE>> states = getStates(transition.getTarget());
		if (states.isEmpty()) {
			return null;
		}
		final Iterator<Pair<CodeBlock, STATE>> iterator = states.iterator();
		final Set<CodeBlock> transitions = new HashSet<>();

		STATE accumulator = null;
		while (iterator.hasNext()) {
			final Pair<CodeBlock, STATE> pair = iterator.next();
			transitions.add(pair.getFirst());
			if (accumulator == null) {
				accumulator = pair.getSecond();
			} else {
				accumulator = mMergeOperator.apply(pair.getSecond(), accumulator);
				assert accumulator.getVariables().keySet()
						.equals(pair.getSecond().getVariables().keySet()) : "states have different variables";
			}
			iterator.remove();
		}

		assert accumulator != null;
		for (final CodeBlock trans : transitions) {
			states.addFirst(new Pair<CodeBlock, STATE>(trans, accumulator));
		}
		assert states.size() == transitions.size();
		return accumulator;
	}

	@Override
	public final IAbstractStateStorage<STATE, CodeBlock, IBoogieVar, ProgramPoint> createStorage() {
		final BaseRcfgAbstractStateStorageProvider<STATE> rtr = create();
		mChildStores.add(rtr);
		return rtr;
	}

	protected abstract BaseRcfgAbstractStateStorageProvider<STATE> create();

	@Override
	public Map<ProgramPoint, Term> getTerms(final CodeBlock initialTransition, final Script script,
			final Boogie2SMT bpl2smt) {
		Map<ProgramPoint, STATE> states = getMergedLocalStates(initialTransition);
		for (final BaseRcfgAbstractStateStorageProvider<STATE> child : mChildStores) {
			states = mergeMaps(states, child.getMergedLocalStates(initialTransition));
		}
		return convertStates2Terms(states, script, bpl2smt);
	}

	private Map<ProgramPoint, STATE> getMergedLocalStates(final CodeBlock initialTransition) {
		final Map<ProgramPoint, STATE> rtr = new HashMap<>();
		final Deque<ProgramPoint> worklist = new ArrayDeque<>();
		final Set<ProgramPoint> closed = new HashSet<>();

		worklist.add((ProgramPoint) initialTransition.getTarget());

		while (!worklist.isEmpty()) {
			final ProgramPoint current = worklist.remove();
			// check if already processed
			if (!closed.add(current)) {
				continue;
			}
			// add successors to worklist
			for (final RCFGEdge outgoing : current.getOutgoingEdges()) {
				if (!(outgoing instanceof CodeBlock)) {
					continue;
				}
				final RCFGNode target = outgoing.getTarget();
				if (!(target instanceof ProgramPoint)) {
					continue;
				}
				final ProgramPoint targetpp = (ProgramPoint) target;
				worklist.add(targetpp);
			}

			final Deque<Pair<CodeBlock, STATE>> states = getStates(current);
			if (states == null) {
				// no states for this location
				continue;
			}
			final Optional<STATE> mergedState = states.stream().map(a -> a.getSecond()).reduce(mMergeOperator::apply);
			if (!mergedState.isPresent()) {
				// no states for this location
				continue;
			}

			// TODO: and or or ???
			STATE currentState = rtr.get(current);
			if (currentState == null) {
				rtr.put(current, mergedState.get());
			} else {
				rtr.put(current, mMergeOperator.apply(mergedState.get(), currentState));
			}
		}
		return rtr;
	}

	private Map<ProgramPoint, STATE> mergeMaps(Map<ProgramPoint, STATE> a, Map<ProgramPoint, STATE> b) {
		final Map<ProgramPoint, STATE> rtr = new HashMap<>();

		for (final Entry<ProgramPoint, STATE> entryA : a.entrySet()) {
			final STATE valueB = b.get(entryA.getKey());
			if (valueB == null) {
				rtr.put(entryA.getKey(), entryA.getValue());
			} else {
				rtr.put(entryA.getKey(), mMergeOperator.apply(entryA.getValue(), valueB));
			}
		}

		for (final Entry<ProgramPoint, STATE> entryB : b.entrySet()) {
			final STATE valueA = a.get(entryB.getKey());
			if (valueA == null) {
				rtr.put(entryB.getKey(), entryB.getValue());
			} else {
				// do nothing, this was already done in first iteration
			}
		}

		return rtr;
	}

	private Map<ProgramPoint, Term> convertStates2Terms(final Map<ProgramPoint, STATE> states, final Script script,
			final Boogie2SMT bpl2smt) {
		final Map<ProgramPoint, Term> rtr = new HashMap<>();

		for (final Entry<ProgramPoint, STATE> entry : states.entrySet()) {
			rtr.put(entry.getKey(), entry.getValue().getTerm(script, bpl2smt));
		}

		return rtr;
	}

	protected List<CodeBlock> getErrorTrace(CodeBlock start, CodeBlock end) {
		// get the trace from the entry codeblock to this codeblock via all the
		// states in between
		assert start != null;
		assert end != null;

		final List<CodeBlock> trace = new ArrayList<>();
		final IHeuristic<RCFGNode, RCFGEdge> heuristic = new ErrorPathHeuristic();
		// TODO: Use a denier that takes the abstract states into account (not allowing empty states)
		final IEdgeDenier<RCFGEdge> denier = new RcfgEdgeDenier();
		final AStar<RCFGNode, RCFGEdge> search = new AStar<RCFGNode, RCFGEdge>(
				mServices.getLoggingService().getLogger(Activator.PLUGIN_ID), start.getSource(), end.getTarget(),
				heuristic, new RcfgWrapper(), denier);
		final List<RCFGEdge> path = search.findPath();

		if (path == null) {
			return Collections.emptyList();
		}

		for (final RCFGEdge elem : path) {
			if (elem instanceof CodeBlock) {
				trace.add((CodeBlock) elem);
			}
		}

		return trace;
	}

	private List<STATE> getAbstractStates(CodeBlock transition, RCFGNode node) {
		assert node != null;
		final Deque<Pair<CodeBlock, STATE>> states = getStates(node);
		final List<STATE> rtr = new ArrayList<STATE>(states.size());
		for (final Pair<CodeBlock, STATE> state : states) {
			rtr.add(state.getSecond());
		}
		return rtr;
	}

	private void addState(CodeBlock transition, STATE state, RCFGNode node) {
		assert node != null;
		assert transition != null;
		assert node.equals(transition.getSource()) || node.equals(transition.getTarget());
		final Deque<Pair<CodeBlock, STATE>> states = getStates(node);
		// TODO: Optimize by removing lower states if they are equal to this one
		states.addFirst(new Pair<CodeBlock, STATE>(transition, state));
	}

	/**
	 * This method extracts the current state at a given node by comparing all the states at this node in the stack
	 * order with the matcher. The stack of states at a node is saved as a pair (transition,state), where the state is
	 * the post state of the transition.
	 * 
	 * @param node
	 * @param matcher
	 * @return
	 */
	private STATE getCurrentState(final RCFGNode node, final IStateMatcher<CodeBlock> matcher) {
		assert node != null;
		final Deque<Pair<CodeBlock, STATE>> states = getStates(node);
		final Iterator<Pair<CodeBlock, STATE>> iterator = states.iterator();
		while (iterator.hasNext()) {
			final Pair<CodeBlock, STATE> current = iterator.next();
			if (matcher.check(current.getFirst())) {
				return current.getSecond();
			}
		}
		return null;
	}

	protected abstract Deque<Pair<CodeBlock, STATE>> getStates(RCFGNode node);

	protected IAbstractStateBinaryOperator<STATE> getMergeOperator() {
		return mMergeOperator;
	}

	protected IUltimateServiceProvider getServices() {
		return mServices;
	}

	private final class ErrorPathHeuristic implements IHeuristic<RCFGNode, RCFGEdge> {
		@Override
		public int getHeuristicValue(RCFGNode from, RCFGEdge over, RCFGNode to) {
			for (Pair<CodeBlock, STATE> pair : getStates(over.getTarget())) {
				if (pair.getFirst().equals(over)) {
					return 0;
				}
			}
			return 1000;
		}

		@Override
		public int getConcreteCost(RCFGEdge edge) {
			for (Pair<CodeBlock, STATE> pair : getStates(edge.getTarget())) {
				if (pair.getFirst().equals(edge)) {
					return 1;
				}
			}
			return 1000;
		}
	}

	private static final class RcfgEdgeDenier implements IEdgeDenier<RCFGEdge> {
		@Override
		public boolean isForbidden(final RCFGEdge edge, final Iterator<RCFGEdge> backpointers) {
			if (edge instanceof Summary) {
				return ((Summary) edge).calledProcedureHasImplementation();
			}

			if (edge instanceof Return) {
				// check if the first call on the path spanned by the
				// backpointers is the call matching this return
				final Call call = ((Return) edge).getCorrespondingCall();
				while (backpointers.hasNext()) {
					final RCFGEdge backpointer = backpointers.next();
					if (call.equals(backpointer)) {
						return false;
					}
				}
				return true;
			}
			return false;
		}
	}

	@FunctionalInterface
	public interface IStateMatcher<T> {
		public boolean check(T current);
	}
}
