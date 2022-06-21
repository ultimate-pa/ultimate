package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.UnaryOperator;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.ParameterizedOrder.Predicate;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class ParameterizedOrderAutomaton<L extends IIcfgTransition<?>>
implements INwaOutgoingLetterAndTransitionProvider<L, IPredicate>{
	private final Map<Predicate, Predicate> mCreatedStates = new HashMap<>();
	private final Set<String> mThreads = new HashSet<>();
	private final Set<IPredicate> mInitialStates = new HashSet<>();
	private static Integer mParameter;
	private final Boolean mIsLoop;
	private Set<L> mAlphabet;
	private String mInitialThread;

	
	public ParameterizedOrderAutomaton(final Integer parameter, final Boolean isLoop, final Set<String> threads, final VpAlphabet<L> alphabet) {
		mParameter = parameter;
		mIsLoop = isLoop;
		mThreads.addAll(threads);
		mAlphabet = alphabet.getInternalAlphabet();
		
	}

	@Override
	public IStateFactory<IPredicate> getStateFactory() {
		throw new UnsupportedOperationException();
	}

	@Override
	public VpAlphabet<L> getVpAlphabet() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IPredicate getEmptyStackState() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterable<IPredicate> getInitialStates() {
		return getOrCreateInitialStates();
	}

	private Iterable<IPredicate> getOrCreateInitialStates() {
		if (mInitialStates.isEmpty()) {
			for (String thread : mThreads) {
				mInitialStates.add((IPredicate) getOrCreateState(thread, 0));
			}
		}
		return mInitialStates;
	}


	private Object getOrCreateState(String thread, Integer counter) {
		Predicate state = new Predicate(thread, counter);
		mCreatedStates.put(state, state);
		return state;
		
	}

	@Override
	public boolean isInitial(IPredicate state) {
		Predicate pState = (Predicate) state;
		return (pState.getThread()==mInitialThread && pState.getCounter()==0);
	}

	@Override
	public boolean isFinal(IPredicate state) {
		return true;
	}

	@Override
	public int size() {
		return -1;
	}

	@Override
	public String sizeInformation() {
		return "<unknown>";
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, IPredicate>> internalSuccessors(IPredicate state, L letter) {
		Predicate pState = (Predicate) state;
		if (mIsLoop) {
			return null;
		}
		else if (pState.getCounter()==mParameter) {
			return getOrCreateState(nextThread(pState.getThread()),0);
		}
		else {
			return getOrCreateState(pState.getThread(),pState.getCounter()+1);
		}
		//missing: distinction for letters of threads that are different to the most priorized
	}

	private String nextThread(String thread) {
		// How can we compute the thread that should come next?
		return null;
	}

	@Override
	public Iterable<OutgoingCallTransition<L, IPredicate>> callSuccessors(IPredicate state, L letter) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterable<OutgoingReturnTransition<L, IPredicate>> returnSuccessors(IPredicate state, IPredicate hier,
			L letter) {
		throw new UnsupportedOperationException();
	}
	
	public static final class Predicate implements IPredicate {
		
		private final String mThread;
		private final Integer mCounter;
		
		public Predicate(final String thread, final Integer counter) {
			mThread = thread;
			mCounter = counter;
		}
		
		public String getThread() {
			return mThread;
		}
		
		public Integer getCounter() {
			return mCounter;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final Predicate other = (Predicate) obj;
			return Objects.equals(mThread, other.mThread) && Objects.equals(mCounter, other.mCounter);
		}

		@Override
		public String[] getProcedures() {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Set<IProgramVar> getVars() {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Term getFormula() {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Term getClosedFormula() {
			// TODO Auto-generated method stub
			return null;
		}
		
	}

}
