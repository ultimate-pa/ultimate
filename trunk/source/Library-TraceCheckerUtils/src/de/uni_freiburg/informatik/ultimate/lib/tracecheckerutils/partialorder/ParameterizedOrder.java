package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.function.UnaryOperator;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.LoopLockstepOrder.PredicateWithLastThread;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class ParameterizedOrder<L extends IIcfgTransition<?>> implements IDfsOrder<L, IPredicate> {

	
	private final Comparator<L> mDefaultComparator =
			Comparator.comparing(L::getPrecedingProcedure).thenComparingInt(Object::hashCode);
	private final IIcfg<?> mIcfg;
	private final UnaryOperator<IPredicate> mNormalize;
	private static Integer mParameter;
	private final Boolean mType;

	@Override
	public Comparator<L> getOrder(IPredicate state) {
		// TODO Auto-generated method stub
		return null;
	}
	@Override
	public boolean isPositional() {
		// TODO Auto-generated method stub
		return true;
	}
	
	public ParameterizedOrder(final IIcfg<?> icfg, final UnaryOperator<IPredicate> normalize, final Integer parameter, final Boolean type) {
		mIcfg = icfg;
		mNormalize = normalize;
		mParameter = parameter;
		mType = type;
	}
	
	
	public INwaOutgoingLetterAndTransitionProvider<L, IPredicate>
			monitor(final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> automaton) {
		assert NestedWordAutomataUtils.isFiniteAutomaton(automaton) : "No calls and returns supported";
		final Optional<String> maxThread =
				IcfgUtils.getAllThreadInstances(mIcfg).stream().min(Comparator.naturalOrder());
		assert maxThread.isPresent() : "No thread found";
		
		return new MonitorAutomaton<>(automaton, maxThread.get());
		}
	
	private static final class MonitorAutomaton<L extends IIcfgTransition<?>>
			implements INwaOutgoingLetterAndTransitionProvider<L, IPredicate>{
		private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mUnderlying;
		private final String mMaxThread;

		private final Map<IPredicate, Map<String, IPredicate>> mKnownStates = new HashMap<>();

		
		private MonitorAutomaton(final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> automaton,
				final String maxThread) {
			mUnderlying = automaton;
			mMaxThread = maxThread;
		}
		
		@Override
		public IStateFactory<IPredicate> getStateFactory() {
			throw new UnsupportedOperationException();
		}

		@Override
		public VpAlphabet<L> getVpAlphabet() {
			return mUnderlying.getVpAlphabet();
		}

		@Override
		public IPredicate getEmptyStackState() {
			throw new UnsupportedOperationException();
		}

		@Override
		public Iterable<IPredicate> getInitialStates() {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public boolean isInitial(IPredicate state) {
			// TODO Auto-generated method stub
			return false;
		}

		@Override
		public boolean isFinal(IPredicate state) {
			// TODO Auto-generated method stub
			return false;
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
			if (!(state instanceof Predicate)) {
				throw new IllegalArgumentException();
			}
			final Predicate predState = (Predicate) state;
			final String lastThread;
			final IcfgLocation target = letter.getTarget();
			final Integer newCounter;
			final Integer oldCounter = predState.mCounter;
			// TODO: What if a letter is of a different thread? -> Reset as well, but how can we detect?
			if (oldCounter == mParameter) {
				lastThread = target.getProcedure();
				newCounter = 0;
			} else {
				lastThread = predState.getLastThread();
				newCounter = oldCounter + 1;
			}
			return StreamSupport
					.stream(mUnderlying.internalSuccessors(predState.getUnderlying(), letter).spliterator(), false)
					.map(outgoing -> new OutgoingInternalTransition<>(letter,
							getOrCreateState(outgoing.getSucc(), lastThread, newCounter)))
					.collect(Collectors.toSet());
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
		
		private IPredicate getOrCreateState(final IPredicate underlying, final String lastThread, final Integer counter) {
			final Map<String, IPredicate> thread2State = mKnownStates.computeIfAbsent(underlying, x -> new HashMap<>());
			return thread2State.computeIfAbsent(lastThread,
					x -> new Predicate((IMLPredicate) underlying, lastThread, counter));
			
		}
		
	}
	
	public static final class Predicate implements IMLPredicate {

		private final IMLPredicate mUnderlying;
		private final String mLastThread;
		private final Integer mCounter;

		public Predicate(final IMLPredicate underlying, final String lastThread, final Integer counter) {
			mUnderlying = underlying;
			mLastThread = lastThread;
			mCounter = counter;
		}

		public IMLPredicate getUnderlying() {
			return mUnderlying;
		}

		public String getLastThread() {
			return mLastThread;
		}
		
		@Override
		public IcfgLocation[] getProgramPoints() {
			return mUnderlying.getProgramPoints();
		}

		@Override
		public Term getFormula() {
			return mUnderlying.getFormula();
		}

		@Override
		public Term getClosedFormula() {
			return mUnderlying.getClosedFormula();
		}

		@Override
		public String[] getProcedures() {
			return mUnderlying.getProcedures();
		}

		@Override
		public Set<IProgramVar> getVars() {
			return mUnderlying.getVars();
		}

		@Override
		public Set<IProgramConst> getConstants() {
			return mUnderlying.getConstants();
		}

		@Override
		public Set<IProgramFunction> getFunctions() {
			return mUnderlying.getFunctions();
		}

		@Override
		public int hashCode() {
			return Objects.hash(mLastThread, mUnderlying, mCounter);
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
			return Objects.equals(mLastThread, other.mLastThread) && Objects.equals(mUnderlying, other.mUnderlying) && Objects.equals(mCounter, other.mCounter);
		}
	}

}

