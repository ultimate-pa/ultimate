package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.Comparator;
import java.util.HashSet;
import java.util.Optional;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

public class ParameterizedOrder<L extends IIcfgTransition<?>> implements IParameterizedOrder<L, IPredicate>{
	private final Set<String> mThreads = new HashSet<>();
	private static Integer mParameter;
	private Set<L> mAlphabet;
	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mParameterizedOrderAutomaton;

	public ParameterizedOrder(Integer parameter) {
		mParameter = parameter;
		mParameterizedOrderAutomaton = new ParameterizedOrderAutomaton(mParameter, mThreads);
	}
	
	@Override
	public Comparator<L> getOrder(IPredicate state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isPositional() {
		return true;
	}

	@Override
	public boolean isStep() {
		// TODO Auto-generated method stub
		return false;
	}
	
	public INwaOutgoingLetterAndTransitionProvider<L, IPredicate> getParameterizedOrderAutomaton() {
		return mParameterizedOrderAutomaton;
	}

}
