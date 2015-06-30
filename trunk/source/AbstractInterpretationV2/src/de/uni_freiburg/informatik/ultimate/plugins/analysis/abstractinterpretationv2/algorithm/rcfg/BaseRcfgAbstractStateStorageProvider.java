package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IAbstractStateStorage;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector.AStar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector.IEdgeDenier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector.IHeuristic;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector.RcfgWrapper;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

public abstract class BaseRcfgAbstractStateStorageProvider implements IAbstractStateStorage<CodeBlock, BoogieVar> {

	private final IAbstractStateBinaryOperator<CodeBlock, BoogieVar> mMergeOperator;
	private final IUltimateServiceProvider mServices;

	public BaseRcfgAbstractStateStorageProvider(IAbstractStateBinaryOperator<CodeBlock, BoogieVar> mergeOperator,
			IUltimateServiceProvider services) {
		assert mergeOperator != null;
		assert services != null;
		mMergeOperator = mergeOperator;
		mServices = services;
	}

	@Override
	public Collection<IAbstractState<CodeBlock, BoogieVar>> getAbstractPreStates(CodeBlock transition) {
		assert transition != null;
		return getAbstractStates(transition, transition.getSource());
	}

	@Override
	public Collection<IAbstractState<CodeBlock, BoogieVar>> getAbstractPostStates(CodeBlock transition) {
		assert transition != null;
		return getAbstractStates(transition, transition.getTarget());
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> getCurrentAbstractPreState(CodeBlock transition) {
		assert transition != null;
		assert transition != null;
		return getCurrentState(transition, transition.getSource());
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> getCurrentAbstractPostState(CodeBlock transition) {
		assert transition != null;
		return getCurrentState(transition, transition.getTarget());
	}

	@Override
	public void addAbstractPreState(CodeBlock transition, IAbstractState<CodeBlock, BoogieVar> state) {
		assert transition != null;
		assert state != null;
		addState(transition, state, transition.getSource());
	}

	@Override
	public void addAbstractPostState(CodeBlock transition, IAbstractState<CodeBlock, BoogieVar> state) {
		assert transition != null;
		assert state != null;
		addState(transition, state, transition.getTarget());
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> setPostStateIsFixpoint(CodeBlock transition,
			IAbstractState<CodeBlock, BoogieVar> state, boolean value) {
		assert transition != null;
		assert state != null;
		final Deque<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>> states = getStates(transition.getTarget());
		assert !states.isEmpty();

		final Iterator<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>> iterator = states.iterator();
		boolean removed = false;
		while (iterator.hasNext()) {
			final Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>> next = iterator.next();
			if (state.equals(next.getSecond())) {
				iterator.remove();
				removed = true;
				break;
			}
		}
		assert removed;
		final IAbstractState<CodeBlock, BoogieVar> rtr = state.setFixpoint(value);
		states.addFirst(new Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>(transition, rtr));
		return rtr;
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> mergePostStates(CodeBlock transition) {
		assert transition != null;
		final Deque<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>> states = getStates(transition.getTarget());
		if (states.isEmpty()) {
			return null;
		}
		final Iterator<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>> iterator = states.iterator();
		final Set<CodeBlock> transitions = new HashSet<>();

		Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>> pair = iterator.next();
		iterator.remove();
		transitions.add(pair.getFirst());
		IAbstractState<CodeBlock, BoogieVar> last;
		IAbstractState<CodeBlock, BoogieVar> current = pair.getSecond();
		while (iterator.hasNext()) {
			pair = iterator.next();
			iterator.remove();
			transitions.add(pair.getFirst());
			last = pair.getSecond();
			current = mMergeOperator.apply(current, last);
		}
		assert current != null;
		for (CodeBlock trans : transitions) {
			states.addFirst(new Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>(trans, current.copy()));
		}
		assert states.size() == transitions.size();
		return current;
	}

	protected List<CodeBlock> getErrorTrace(CodeBlock start, CodeBlock end) {
		// get the trace from the entry codeblock to this codeblock via all the
		// states in between
		assert start != null;
		assert end != null;

		final List<CodeBlock> trace = new ArrayList<>();
		final IHeuristic<RCFGNode, RCFGEdge> heuristic = new ErrorPathHeuristic();
		final IEdgeDenier<RCFGEdge> denier = new RcfgEdgeDenier();
		final AStar<RCFGNode, RCFGEdge> search = new AStar<RCFGNode, RCFGEdge>(mServices.getLoggingService().getLogger(
				Activator.PLUGIN_ID), start.getSource(), end.getTarget(), heuristic, new RcfgWrapper(), denier);
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

	private Collection<IAbstractState<CodeBlock, BoogieVar>> getAbstractStates(CodeBlock transition, RCFGNode node) {
		assert node != null;
		final Deque<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>> states = getStates(node);
		final Collection<IAbstractState<CodeBlock, BoogieVar>> rtr = new ArrayList<IAbstractState<CodeBlock, BoogieVar>>(
				states.size());
		for (final Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>> state : states) {
			rtr.add(state.getSecond());
		}
		return rtr;
	}

	private void addState(CodeBlock transition, IAbstractState<CodeBlock, BoogieVar> state, RCFGNode node) {
		assert node != null;
		final Deque<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>> states = getStates(node);
		// TODO: Optimize by removing lower states if they are equal to this one
		states.addFirst(new Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>(transition, state));
	}

	private IAbstractState<CodeBlock, BoogieVar> getCurrentState(CodeBlock transition, RCFGNode node) {
		assert node != null;
		final Deque<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>> states = getStates(node);
		final Iterator<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>> iterator = states.iterator();
		while (iterator.hasNext()) {
			final Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>> current = iterator.next();
			if (current.getFirst().equals(transition)) {
				return current.getSecond();
			}
		}
		return null;
	}

	protected abstract Deque<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>> getStates(RCFGNode node);

	protected IAbstractStateBinaryOperator<CodeBlock, BoogieVar> getMergeOperator() {
		return mMergeOperator;
	}

	protected IUltimateServiceProvider getServices() {
		return mServices;
	}

	private final class ErrorPathHeuristic implements IHeuristic<RCFGNode, RCFGEdge> {
		@Override
		public int getHeuristicValue(RCFGNode from, RCFGEdge over, RCFGNode to) {
			for (Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>> pair : getStates(over.getTarget())) {
				if (pair.getFirst().equals(over)) {
					return 0;
				}
			}
			return 1000;
		}

		@Override
		public int getConcreteCost(RCFGEdge edge) {
			for (Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>> pair : getStates(edge.getTarget())) {
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
}
