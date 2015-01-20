package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender;

import java.util.Collection;
import java.util.Collections;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomatonCache;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NwaCacheBookkeeping;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker.HTTV;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SdHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

/**
 * Superclass for interpolant automata that are build on-the-fly.
 * 
 * @author Matthias Heizmann
 * 
 */
public abstract class AbstractInterpolantAutomaton2 implements INestedWordAutomatonSimple<CodeBlock, IPredicate> {
	
	public enum Mode { ON_DEMAND_CONSTRUCTION, READ_ONLY }

	protected final IUltimateServiceProvider m_Services;
	protected final Logger mLogger;

	protected final SmtManager m_SmtManager;
	protected final IHoareTripleChecker m_IHoareTripleChecker;
	protected final SdHoareTripleChecker m_EdgeChecker;
	protected final IPredicate m_IaFalseState;
	protected final NestedWordAutomatonCache<CodeBlock, IPredicate> m_Result;
	protected final NestedWordAutomaton<CodeBlock, IPredicate> m_InterpolantAutomaton;

	private Mode m_Mode = Mode.ON_DEMAND_CONSTRUCTION;

	private final InternalSuccessorComputationHelper m_InSucComp;
	private final CallSuccessorComputationHelper m_CaSucComp;
	private final ReturnSuccessorComputationHelper m_ReSucComp;

	public AbstractInterpolantAutomaton2(IUltimateServiceProvider services, 
			SmtManager smtManager, ModifiableGlobalVariableManager modglobvarman, IHoareTripleChecker hoareTripleChecker,
			INestedWordAutomaton<CodeBlock, IPredicate> abstraction, IPredicate falseState,
			NestedWordAutomaton<CodeBlock, IPredicate> interpolantAutomaton, Logger logger) {
		super();
		m_Services = services;
		mLogger = logger;
		m_SmtManager = smtManager;
		m_EdgeChecker = new SdHoareTripleChecker(modglobvarman);
		m_IHoareTripleChecker = hoareTripleChecker;
		m_IaFalseState = falseState;
		m_InterpolantAutomaton = interpolantAutomaton;
		m_InSucComp = new InternalSuccessorComputationHelper();
		m_CaSucComp = new CallSuccessorComputationHelper();
		m_ReSucComp = new ReturnSuccessorComputationHelper();
		m_Result = new NestedWordAutomatonCache<CodeBlock, IPredicate>(m_Services, abstraction.getInternalAlphabet(),
				abstraction.getCallAlphabet(), abstraction.getReturnAlphabet(), abstraction.getStateFactory());
	}

	/**
	 * Switch the mode to READ_ONLY. In this mode the automaton returns
	 * only existing transitions but does not compute new ones.
	 */
	public final void switchToReadonlyMode() {
		if (m_Mode == Mode.READ_ONLY) {
			throw new AssertionError("already in mode READ_ONLY");
		} else {
			m_Mode = Mode.READ_ONLY;
			mLogger.info(switchToReadonlyMessage());
		}
	}
	
	/**
	 * Switch the mode to ON_DEMAND_CONSTRUCTION. In this mode the automaton
	 * behaves as follows:
	 * If the automaton is asked if a transition exists, the automaton checks
	 * the rules that define this automaton (validity of Hoare triples) and
	 * constructs the transition on demand.
	 */
	public final void switchToOnDemandConstructionMode() {
		if (m_Mode == Mode.ON_DEMAND_CONSTRUCTION) {
			throw new AssertionError("already in mode ON_DEMAND_CONSTRUCTION");
		} else {
			m_Mode = Mode.ON_DEMAND_CONSTRUCTION;
			mLogger.info(switchToOnTheFlyConstructionMessage());
		}
	}
	

	protected abstract String startMessage();

	protected abstract String switchToReadonlyMessage();
	
	protected abstract String switchToOnTheFlyConstructionMessage();


	@Override
	public final int size() {
		return m_Result.size();
	}

	@Override
	public final Set<CodeBlock> getAlphabet() {
		return m_Result.getAlphabet();
	}

	@Override
	public final String sizeInformation() {
		return m_Result.sizeInformation();
	}

	@Override
	public final Set<CodeBlock> getInternalAlphabet() {
		return m_Result.getInternalAlphabet();
	}

	@Override
	public final Set<CodeBlock> getCallAlphabet() {
		return m_Result.getCallAlphabet();
	}

	@Override
	public final Set<CodeBlock> getReturnAlphabet() {
		return m_Result.getReturnAlphabet();
	}

	@Override
	public final StateFactory<IPredicate> getStateFactory() {
		return m_Result.getStateFactory();
	}

	@Override
	public final IPredicate getEmptyStackState() {
		return m_Result.getEmptyStackState();
	}

	@Override
	public final Iterable<IPredicate> getInitialStates() {
		return m_Result.getInitialStates();
	}

	@Override
	public final boolean isInitial(IPredicate state) {
		return m_Result.isInitial(state);
	}

	@Override
	public final boolean isFinal(IPredicate state) {
		return m_Result.isFinal(state);
	}

	@Override
	public final Set<CodeBlock> lettersInternal(IPredicate state) {
		return getInternalAlphabet();
	}

	@Override
	public final Set<CodeBlock> lettersCall(IPredicate state) {
		return getCallAlphabet();
	}

	@Override
	public final Set<CodeBlock> lettersReturn(IPredicate state) {
		return getReturnAlphabet();
	}

	@Override
	public final Iterable<OutgoingInternalTransition<CodeBlock, IPredicate>> internalSuccessors(IPredicate state,
			CodeBlock letter) {
		if (m_Mode == Mode.ON_DEMAND_CONSTRUCTION) {
			if (!areInternalSuccsComputed(state, letter)) {
				computeSuccs(state, null, letter, m_InSucComp);
			}
		}
		return m_Result.internalSuccessors(state, letter);
	}

	protected abstract void computeSuccs(IPredicate state, IPredicate hier, CodeBlock ret,
			SuccessorComputationHelper sch);

	/**
	 * Have the internal successors of state and letter already been computed.
	 */
	protected abstract boolean areInternalSuccsComputed(IPredicate state, CodeBlock letter);

	@Override
	public final Iterable<OutgoingInternalTransition<CodeBlock, IPredicate>> internalSuccessors(IPredicate state) {
		if (m_Mode == Mode.ON_DEMAND_CONSTRUCTION) {
			for (CodeBlock letter : lettersInternal(state)) {
				if (!areInternalSuccsComputed(state, letter)) {
					computeSuccs(state, null, letter, m_InSucComp);
				}
			}
		}
		return m_Result.internalSuccessors(state);
	}

	@Override
	public final Iterable<OutgoingCallTransition<CodeBlock, IPredicate>> callSuccessors(IPredicate state,
			CodeBlock letter) {
		Call call = (Call) letter;
		if (m_Mode == Mode.ON_DEMAND_CONSTRUCTION) {
			if (!areCallSuccsComputed(state, call)) {
				computeSuccs(state, null, letter, m_CaSucComp);
			}
		}
		return m_Result.callSuccessors(state, call);
	}

	/**
	 * Have the call successors of state and call already been computed.
	 */
	protected abstract boolean areCallSuccsComputed(IPredicate state, Call call);

	@Override
	public final Iterable<OutgoingCallTransition<CodeBlock, IPredicate>> callSuccessors(IPredicate state) {
		if (m_Mode == Mode.ON_DEMAND_CONSTRUCTION) {
			for (CodeBlock letter : lettersCall(state)) {
				Call call = (Call) letter;
				if (!m_Result.callSuccessors(state, call).iterator().hasNext()) {
					computeSuccs(state, null, letter, m_CaSucComp);
				}
			}
		}
		return m_Result.callSuccessors(state);
	}

	@Override
	public final Iterable<OutgoingReturnTransition<CodeBlock, IPredicate>> returnSucccessors(IPredicate state,
			IPredicate hier, CodeBlock letter) {
		Return ret = (Return) letter;
		if (m_Mode == Mode.ON_DEMAND_CONSTRUCTION) {
			if (!areReturnSuccsComputed(state, hier, ret)) {
				computeSuccs(state, hier, letter, m_ReSucComp);
			}
		}
		return m_Result.returnSucccessors(state, hier, ret);
	}

	/**
	 * Have the return successors of state, hier and ret already been computed.
	 */
	protected abstract boolean areReturnSuccsComputed(IPredicate state, IPredicate hier, Return ret);

	@Override
	public final Iterable<OutgoingReturnTransition<CodeBlock, IPredicate>> returnSuccessorsGivenHier(IPredicate state,
			IPredicate hier) {
		if (m_Mode == Mode.ON_DEMAND_CONSTRUCTION) {
			for (CodeBlock letter : lettersReturn(state)) {
				Return ret = (Return) letter;
				if (!m_Result.returnSucccessors(state, hier, ret).iterator().hasNext()) {
					computeSuccs(state, hier, letter, m_ReSucComp);
				}
			}
		}
		return m_Result.returnSuccessorsGivenHier(state, hier);
	}

	@Override
	public final String toString() {
		if (m_Mode == Mode.READ_ONLY) {
			return (new AtsDefinitionPrinter<String, String>(m_Services, "nwa", this)).getDefinitionAsString();
		} else {
			return "automaton under construction";
		}
	}

	/**
	 * Abstract class for successor computation. Subclasses are the successor
	 * computations for internal, call, and return. Because we can only override
	 * methods with the same signature (in Java) we use the
	 * 3-parameter-signature for return (with hierarchical state) and use null
	 * as hierarchical state for call and internal.
	 */
	public abstract class SuccessorComputationHelper {

		public abstract boolean isLinearPredecessorFalse(IPredicate resPred);

		public abstract boolean isHierarchicalPredecessorFalse(IPredicate resPred);

		public abstract void addTransition(IPredicate resPred, IPredicate resHier, CodeBlock letter,
				IPredicate iaFalseState);

		public abstract HTTV computeSuccWithSolver(IPredicate resPred, IPredicate resHier, CodeBlock letter,
				IPredicate iaFalseState);

		public abstract HTTV sdecToFalse(IPredicate resPred, IPredicate resHier, CodeBlock letter);

		public abstract Collection<IPredicate> getSuccsInterpolantAutomaton(IPredicate resPred, IPredicate resHier,
				CodeBlock letter);

		public abstract boolean isInductiveSefloop(IPredicate resPred, IPredicate resHier, CodeBlock letter,
				IPredicate succCand);

		public abstract HTTV sdec(IPredicate resPred, IPredicate resHier, CodeBlock letter, IPredicate succCand);

		public abstract HTTV sdLazyEc(IPredicate resPred, IPredicate resHier, CodeBlock letter, IPredicate succCand);

		public abstract boolean reviewResult(IPredicate resPred, IPredicate resHier, CodeBlock letter,
				IPredicate succCand, HTTV result);

		public abstract void reportCacheEntry(IPredicate resPred, IPredicate resHier, CodeBlock letter,
				NwaCacheBookkeeping<CodeBlock, IPredicate> cacheBookkeeping);
	}

	protected class InternalSuccessorComputationHelper extends SuccessorComputationHelper {

		@Override
		public boolean isLinearPredecessorFalse(IPredicate resPred) {
			return resPred == m_IaFalseState;
		}

		@Override
		public boolean isHierarchicalPredecessorFalse(IPredicate resHier) {
			assert resHier == null;
			return false;
		}

		@Override
		public void addTransition(IPredicate resPred, IPredicate resHier, CodeBlock letter, IPredicate inputSucc) {
			assert resHier == null;
			m_Result.addInternalTransition(resPred, letter, inputSucc);
		}

		@Override
		public HTTV computeSuccWithSolver(IPredicate resPred, IPredicate resHier, CodeBlock letter,
				IPredicate inputSucc) {
			assert resHier == null;
			return m_IHoareTripleChecker.checkInternal(resPred, letter, inputSucc);
		}

		@Override
		public HTTV sdecToFalse(IPredicate resPred, IPredicate resHier, CodeBlock letter) {
			assert resHier == null;
			return m_EdgeChecker.sdecInternalToFalse(resPred, letter);
		}

		@Override
		public Collection<IPredicate> getSuccsInterpolantAutomaton(IPredicate resPred, IPredicate resHier,
				CodeBlock letter) {
			assert resHier == null;
			Collection<IPredicate> succs = m_InterpolantAutomaton.succInternal(resPred, letter);
			if (succs == null) {
				return Collections.emptySet();
			} else {
				return succs;
			}
		}

		@Override
		public boolean isInductiveSefloop(IPredicate resPred, IPredicate resHier, CodeBlock letter, IPredicate succCand) {
			assert resHier == null;
			if ((resPred == succCand) && (m_EdgeChecker.sdecInternalSelfloop(resPred, letter) == HTTV.VALID)) {
				return true;
			} else {
				return false;
			}
		}

		@Override
		public HTTV sdec(IPredicate resPred, IPredicate resHier, CodeBlock letter, IPredicate succCand) {
			assert resHier == null;
			return m_EdgeChecker.sdecInteral(resPred, letter, succCand);
		}

		@Override
		public HTTV sdLazyEc(IPredicate resPred, IPredicate resHier, CodeBlock letter, IPredicate succCand) {
			assert resHier == null;
			return m_EdgeChecker.sdLazyEcInteral(resPred, letter, succCand);
		}

		@Override
		public boolean reviewResult(IPredicate resPred, IPredicate resHier, CodeBlock letter, IPredicate succCand,
				HTTV result) {
			assert resHier == null;
			return reviewInductiveInternal(resPred, letter, succCand, result);
		}

		@Override
		public void reportCacheEntry(IPredicate resPred, IPredicate resHier, CodeBlock letter,
				NwaCacheBookkeeping<CodeBlock, IPredicate> cacheBookkeeping) {
			assert resHier == null;
			cacheBookkeeping.reportCachedInternal(resPred, letter);
		}

	}

	protected class CallSuccessorComputationHelper extends SuccessorComputationHelper {

		@Override
		public boolean isLinearPredecessorFalse(IPredicate resPred) {
			return resPred == m_IaFalseState;
		}

		@Override
		public boolean isHierarchicalPredecessorFalse(IPredicate resHier) {
			assert resHier == null;
			return false;
		}

		@Override
		public void addTransition(IPredicate resPred, IPredicate resHier, CodeBlock letter, IPredicate inputSucc) {
			assert resHier == null;
			m_Result.addCallTransition(resPred, letter, inputSucc);
		}

		@Override
		public HTTV computeSuccWithSolver(IPredicate resPred, IPredicate resHier, CodeBlock letter,
				IPredicate inputSucc) {
			assert resHier == null;
			return m_IHoareTripleChecker.checkCall(resPred, letter, inputSucc);
		}

		@Override
		public HTTV sdecToFalse(IPredicate resPred, IPredicate resHier, CodeBlock letter) {
			assert resHier == null;
			return m_EdgeChecker.sdecCallToFalse(resPred, letter);
		}

		@Override
		public Collection<IPredicate> getSuccsInterpolantAutomaton(IPredicate resPred, IPredicate resHier,
				CodeBlock letter) {
			assert resHier == null;
			Collection<IPredicate> succs = m_InterpolantAutomaton.succCall(resPred, letter);
			if (succs == null) {
				return Collections.emptySet();
			} else {
				return succs;
			}
		}

		@Override
		public boolean isInductiveSefloop(IPredicate resPred, IPredicate resHier, CodeBlock letter, IPredicate succCand) {
			assert resHier == null;
			if ((resPred == succCand) && (m_EdgeChecker.sdecCallSelfloop(resPred, letter) == HTTV.VALID)) {
				return true;
			} else {
				return false;
			}
		}

		@Override
		public HTTV sdec(IPredicate resPred, IPredicate resHier, CodeBlock letter, IPredicate succCand) {
			assert resHier == null;
			return m_EdgeChecker.sdecCall(resPred, letter, succCand);
		}

		@Override
		public HTTV sdLazyEc(IPredicate resPred, IPredicate resHier, CodeBlock letter, IPredicate succCand) {
			assert resHier == null;
			return m_EdgeChecker.sdLazyEcCall(resPred, (Call) letter, succCand);
		}

		@Override
		public boolean reviewResult(IPredicate resPred, IPredicate resHier, CodeBlock letter, IPredicate succCand,
				HTTV result) {
			assert resHier == null;
			return reviewInductiveCall(resPred, (Call) letter, succCand, result);
		}

		@Override
		public void reportCacheEntry(IPredicate resPred, IPredicate resHier, CodeBlock letter,
				NwaCacheBookkeeping<CodeBlock, IPredicate> cacheBookkeeping) {
			assert resHier == null;
			cacheBookkeeping.reportCachedCall(resPred, letter);
		}
	}

	public class ReturnSuccessorComputationHelper extends SuccessorComputationHelper {

		@Override
		public boolean isLinearPredecessorFalse(IPredicate resPred) {
			return resPred == m_IaFalseState;
		}

		@Override
		public boolean isHierarchicalPredecessorFalse(IPredicate resHier) {
			return resHier == m_IaFalseState;
		}

		@Override
		public void addTransition(IPredicate resPred, IPredicate resHier, CodeBlock letter, IPredicate inputSucc) {
			m_Result.addReturnTransition(resPred, resHier, letter, inputSucc);
		}

		@Override
		public HTTV computeSuccWithSolver(IPredicate resPred, IPredicate resHier, CodeBlock letter,
				IPredicate inputSucc) {
			return m_IHoareTripleChecker.checkReturn(resPred, resHier, letter, inputSucc);
		}

		@Override
		public HTTV sdecToFalse(IPredicate resPred, IPredicate resHier, CodeBlock letter) {
			// sat if (not only if!) resPred and resHier are independent,
			// hence we can use the "normal" sdec method
			return m_EdgeChecker.sdecReturn(resPred, resHier, letter, m_IaFalseState);
		}

		@Override
		public Collection<IPredicate> getSuccsInterpolantAutomaton(IPredicate resPred, IPredicate resHier,
				CodeBlock letter) {
			Collection<IPredicate> succs = m_InterpolantAutomaton.succReturn(resPred, resHier, letter);
			if (succs == null) {
				return Collections.emptySet();
			} else {
				return succs;
			}
		}

		@Override
		public boolean isInductiveSefloop(IPredicate resPred, IPredicate resHier, CodeBlock letter, IPredicate succCand) {
			if ((resPred == succCand) && (m_EdgeChecker.sdecReturnSelfloopPre(resPred, (Return) letter) == HTTV.VALID)) {
				return true;
			} else if ((resHier == succCand)
					&& (m_EdgeChecker.sdecReturnSelfloopHier(resHier, (Return) letter) == HTTV.VALID)) {
				return true;
			} else {
				return false;
			}
		}

		@Override
		public HTTV sdec(IPredicate resPred, IPredicate resHier, CodeBlock letter, IPredicate succCand) {
			return m_EdgeChecker.sdecReturn(resPred, resHier, letter, succCand);
		}

		@Override
		public HTTV sdLazyEc(IPredicate resPred, IPredicate resHier, CodeBlock letter, IPredicate succCand) {
			return m_EdgeChecker.sdLazyEcReturn(resPred, resHier, (Return) letter, succCand);
		}

		@Override
		public boolean reviewResult(IPredicate resPred, IPredicate resHier, CodeBlock letter, IPredicate succCand,
				HTTV result) {
			return reviewInductiveReturn(resPred, resHier, (Return) letter, succCand, result);
		}

		@Override
		public void reportCacheEntry(IPredicate resPred, IPredicate resHier, CodeBlock letter,
				NwaCacheBookkeeping<CodeBlock, IPredicate> cacheBookkeeping) {
			cacheBookkeeping.reportCachedReturn(resPred, resHier, letter);
		}

	}

	protected abstract boolean reviewInductiveInternal(IPredicate resPred, CodeBlock letter, IPredicate succCand,
			HTTV result);

	protected abstract boolean reviewInductiveCall(IPredicate resPred, Call letter, IPredicate succCand, HTTV result);

	protected abstract boolean reviewInductiveReturn(IPredicate resPred, IPredicate resHier, Return letter,
			IPredicate succCand, HTTV result);

}
