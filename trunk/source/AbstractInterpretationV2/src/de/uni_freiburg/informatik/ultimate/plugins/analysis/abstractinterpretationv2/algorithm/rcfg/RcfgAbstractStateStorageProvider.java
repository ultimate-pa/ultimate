package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

public class RcfgAbstractStateStorageProvider extends BaseRcfgAbstractStateStorageProvider {

	private final Map<RCFGNode, Deque<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>>> mStorage;

	public RcfgAbstractStateStorageProvider(IAbstractStateBinaryOperator<CodeBlock, BoogieVar> mergeOperator) {
		super(mergeOperator);
		mStorage = new HashMap<RCFGNode, Deque<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>>>();
	}

	protected Deque<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>> getStates(RCFGNode node) {
		assert node != null;
		Deque<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>> rtr = mStorage.get(node);
		if (rtr == null) {
			rtr = new ArrayDeque<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>>();
			mStorage.put(node, rtr);
		}
		return rtr;
	}
}
