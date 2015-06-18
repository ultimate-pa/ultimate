package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IAbstractStateStorage;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

public class RcfgAbstractStateStorageProvider implements IAbstractStateStorage<CodeBlock, BoogieVar> {

	private final Map<RCFGNode, Deque<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>>> mStorage;
	private final IAbstractStateBinaryOperator<CodeBlock, BoogieVar> mMergeOperator;

	public RcfgAbstractStateStorageProvider(IAbstractStateBinaryOperator<CodeBlock, BoogieVar> mergeOperator) {
		assert mergeOperator != null;
		mStorage = new HashMap<RCFGNode, Deque<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>>>();
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
	public void setPostStateIsFixpoint(CodeBlock transition, IAbstractState<CodeBlock, BoogieVar> state, boolean value) {
		assert transition != null;
		assert state != null;
		final Deque<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>> states = getStates(transition.getTarget());
		assert !states.isEmpty();
		assert state.equals(states.getFirst().getSecond());
		states.removeFirst();
		states.addFirst(new Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>(transition, state.setFixpoint(value)));
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

	private Deque<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>> getStates(RCFGNode node) {
		assert node != null;
		Deque<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>> rtr = mStorage.get(node);
		if (rtr == null) {
			rtr = new ArrayDeque<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>>();
			mStorage.put(node, rtr);
		}
		return rtr;
	}
}
