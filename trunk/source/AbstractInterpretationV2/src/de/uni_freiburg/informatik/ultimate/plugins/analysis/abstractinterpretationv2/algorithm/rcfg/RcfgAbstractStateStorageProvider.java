package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IAbstractStateStorage;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;

public class RcfgAbstractStateStorageProvider implements IAbstractStateStorage<CodeBlock, BoogieVar> {

	private final Map<RCFGNode, Deque<IAbstractState<CodeBlock, BoogieVar>>> mStorage;
	private final IAbstractStateBinaryOperator<CodeBlock, BoogieVar> mMergeOperator;

	public RcfgAbstractStateStorageProvider(IAbstractStateBinaryOperator<CodeBlock, BoogieVar> mergeOperator) {
		assert mergeOperator != null;
		mStorage = new HashMap<RCFGNode, Deque<IAbstractState<CodeBlock, BoogieVar>>>();
		mMergeOperator = mergeOperator;
	}

	@Override
	public Collection<IAbstractState<CodeBlock, BoogieVar>> getAbstractPreStates(CodeBlock transition) {
		assert transition != null;
		return getStates(transition.getSource());
	}

	@Override
	public Collection<IAbstractState<CodeBlock, BoogieVar>> getAbstractPostStates(CodeBlock transition) {
		assert transition != null;
		return getStates(transition.getTarget());
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> getCurrentAbstractPreState(CodeBlock transition) {
		assert transition != null;
		Deque<IAbstractState<CodeBlock, BoogieVar>> states = getStates(transition.getSource());
		return states.peekFirst();
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> getCurrentAbstractPostState(CodeBlock transition) {
		assert transition != null;
		Deque<IAbstractState<CodeBlock, BoogieVar>> states = getStates(transition.getTarget());
		return states.peekFirst();
	}

	@Override
	public void addAbstractPreState(CodeBlock transition, IAbstractState<CodeBlock, BoogieVar> state) {
		assert transition != null;
		assert state != null;
		Deque<IAbstractState<CodeBlock, BoogieVar>> states = getStates(transition.getSource());
		states.addFirst(state);
	}

	@Override
	public void addAbstractPostState(CodeBlock transition, IAbstractState<CodeBlock, BoogieVar> state) {
		assert transition != null;
		assert state != null;
		Deque<IAbstractState<CodeBlock, BoogieVar>> states = getStates(transition.getTarget());
		states.addFirst(state);
	}

	@Override
	public void setPostStateIsFixpoint(CodeBlock transition, IAbstractState<CodeBlock, BoogieVar> state, boolean value) {
		assert transition != null;
		assert state != null;
		final Deque<IAbstractState<CodeBlock, BoogieVar>> states = getStates(transition.getTarget());
		assert state.equals(states.getFirst());
		states.removeFirst();
		states.addFirst(state.setFixpoint(value));
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> mergePostStates(CodeBlock transition) {
		assert transition != null;
		Deque<IAbstractState<CodeBlock, BoogieVar>> states = getStates(transition.getTarget());
		if (states.isEmpty()) {
			return null;
		}
		final Iterator<IAbstractState<CodeBlock, BoogieVar>> iterator = states.iterator();
		IAbstractState<CodeBlock, BoogieVar> last;
		IAbstractState<CodeBlock, BoogieVar> current = iterator.next();
		iterator.remove();
		while (iterator.hasNext()) {
			last = iterator.next();
			iterator.remove();
			current = mMergeOperator.apply(current, last);
		}
		assert current != null;
		states.addFirst(current);
		assert states.size() == 1;
		return current;
	}

	private Deque<IAbstractState<CodeBlock, BoogieVar>> getStates(RCFGNode node) {
		assert node != null;
		Deque<IAbstractState<CodeBlock, BoogieVar>> rtr = mStorage.get(node);
		if (rtr == null) {
			rtr = new ArrayDeque<IAbstractState<CodeBlock, BoogieVar>>();
			mStorage.put(node, rtr);
		}
		return rtr;
	}
}
