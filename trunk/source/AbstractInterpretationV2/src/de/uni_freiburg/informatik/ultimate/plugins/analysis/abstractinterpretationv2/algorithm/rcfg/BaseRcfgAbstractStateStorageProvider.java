package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IAbstractStateStorage;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

public abstract class BaseRcfgAbstractStateStorageProvider implements IAbstractStateStorage<CodeBlock, BoogieVar> {
	private final IAbstractStateBinaryOperator<CodeBlock, BoogieVar> mMergeOperator;

	public BaseRcfgAbstractStateStorageProvider(IAbstractStateBinaryOperator<CodeBlock, BoogieVar> mergeOperator) {
		assert mergeOperator != null;
		mMergeOperator = mergeOperator;
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

	protected List<CodeBlock> getTrace(CodeBlock start, CodeBlock end) {
		// get the trace from the entry codeblock to this codeblock via all the
		// states in between
		assert start != null;
		assert end != null;

		final List<CodeBlock> trace = new ArrayList<>();
		final HashSet<CodeBlock> closed = new HashSet<>();
		trace.add(end);
		Deque<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>> possiblePreStates = getStates(end.getSource());
		Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>> searchResult = search(start, possiblePreStates);
//		while (searchResult == null) {
//			for(final Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>> current: possiblePreStates){
//				final CodeBlock traceElement = current.getFirst();
//				if(!closed.add(traceElement)){
//					continue;
//				}
//				trace.add(traceElement);
//				possiblePreStates = getStates(traceElement.getSource());
//				searchResult = search(start, possiblePreStates);
//				break;
//			}
//		}

		Collections.reverse(trace);
		return trace;

	}

	private Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>> search(CodeBlock target,
			Deque<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>> states) {

		if (states == null) {
			return null;
		}
		for (Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>> pair : states) {
			if (pair.getFirst().equals(target)) {
				return pair;
			}
		}
		return null;

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
}
