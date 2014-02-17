package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender;

import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomatonCache;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

/**
 * Superclass for interpolant automata that are build on-the-fly.
 * @author Matthias Heizmann
 *
 */
public abstract class AbstractInterpolantAutomaton implements
		INestedWordAutomatonSimple<CodeBlock, IPredicate> {
	
	protected final static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	protected final SmtManager m_SmtManager;
	protected final EdgeChecker m_EdgeChecker;
	protected final NestedWordAutomatonCache<CodeBlock, IPredicate> m_Result;

	private boolean m_ComputationFinished = false;
	
	private CodeBlock m_AssertedCodeBlock;
	private IPredicate m_AssertedState;
	private IPredicate m_AssertedHier;
	
	public AbstractInterpolantAutomaton(SmtManager smtManager, EdgeChecker edgeChecker,
			INestedWordAutomaton<CodeBlock, IPredicate> abstraction) {
		super();
		m_SmtManager = smtManager;
		m_EdgeChecker = edgeChecker;
		m_Result = new NestedWordAutomatonCache<CodeBlock, IPredicate>(
				abstraction.getInternalAlphabet(), 
				abstraction.getCallAlphabet(), 
				abstraction.getReturnAlphabet(), 
				abstraction.getStateFactory());
	}
	
	
	/**
	 * Announce that computation is finished. From now on this automaton
	 * returns only existing transitions but does not compute new ones.
	 */
	public final void finishConstruction() {
		if (m_ComputationFinished) {
			throw new AssertionError("Computation already finished.");
		} else {
			m_ComputationFinished = true;
			clearAssertionStack();
			s_Logger.info(exitMessage());
		}
	}
	
	protected abstract String exitMessage();


	
	protected final LBool computeSuccInternalSolver(IPredicate state, CodeBlock symbol, IPredicate succCand) {
		if (m_AssertedHier != null) {
			m_EdgeChecker.unAssertHierPred();
			m_AssertedHier = null;
		}
		if (m_AssertedState != state || m_AssertedCodeBlock != symbol) {
			if (m_AssertedState != null) {
				m_EdgeChecker.unAssertPrecondition();
			}
			if (m_AssertedCodeBlock != symbol) {
				if (m_AssertedCodeBlock != null) {
					m_EdgeChecker.unAssertCodeBlock();
				}
				m_EdgeChecker.assertCodeBlock(symbol);
				m_AssertedCodeBlock = symbol;
			}
			m_EdgeChecker.assertPrecondition(state);
			m_AssertedState = state;
		}
		assert m_AssertedState == state && m_AssertedCodeBlock == symbol;
		LBool result = m_EdgeChecker.postInternalImplies(succCand);
		return result;
	}
	
	
	protected final LBool computeSuccCallSolver(IPredicate state, CodeBlock symbol, IPredicate succCand) {
		if (m_AssertedHier != null) {
			m_EdgeChecker.unAssertHierPred();
			m_AssertedHier = null;
		}
		if (m_AssertedState != state || m_AssertedCodeBlock != symbol) {
			if (m_AssertedState != null) {
				m_EdgeChecker.unAssertPrecondition();
			}
			if (m_AssertedCodeBlock != symbol) {
				if (m_AssertedCodeBlock != null) {
					m_EdgeChecker.unAssertCodeBlock();
				}
				m_EdgeChecker.assertCodeBlock(symbol);
				m_AssertedCodeBlock = symbol;
			}
			m_EdgeChecker.assertPrecondition(state);
			m_AssertedState = state;
		}
		assert m_AssertedState == state && m_AssertedCodeBlock == symbol;
		LBool result = m_EdgeChecker.postCallImplies(succCand);
		return result;
	}
	
	
	protected final LBool computeSuccReturnSolver(IPredicate state, IPredicate hier, CodeBlock symbol, IPredicate succCand) {
		if (m_AssertedHier != hier || m_AssertedState != state || m_AssertedCodeBlock != symbol) {
			if (m_AssertedHier != null) {
				m_EdgeChecker.unAssertHierPred();
			}
			if (m_AssertedState != state || m_AssertedCodeBlock != symbol) {
				if (m_AssertedState != null) {
					m_EdgeChecker.unAssertPrecondition();
				}
				if (m_AssertedCodeBlock != symbol) {
					if (m_AssertedCodeBlock != null) {
						m_EdgeChecker.unAssertCodeBlock();
					}
					m_EdgeChecker.assertCodeBlock(symbol);
					m_AssertedCodeBlock = symbol;
				}
				m_EdgeChecker.assertPrecondition(state);
				m_AssertedState = state;
			}
			m_EdgeChecker.assertHierPred(hier);
			m_AssertedHier = hier;
		}
		assert m_AssertedState == state && m_AssertedHier == hier && m_AssertedCodeBlock == symbol;
		LBool result = m_EdgeChecker.postReturnImplies(succCand);
		return result;
	}
	
	
	
	
	protected void clearAssertionStack() {
		if (m_AssertedState != null) {
			m_EdgeChecker.unAssertPrecondition();
			m_AssertedState = null;
		}
		if (m_AssertedHier != null) {
			m_EdgeChecker.unAssertHierPred();
			m_AssertedHier = null;
		}
		if (m_AssertedCodeBlock != null) {
			m_EdgeChecker.unAssertCodeBlock();
			m_AssertedCodeBlock = null;
		}
	}

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
	public final Iterable<OutgoingInternalTransition<CodeBlock, IPredicate>> internalSuccessors(
			IPredicate state, CodeBlock letter) {
		if (!m_ComputationFinished) {
			if (!areInternalSuccsComputed(state, letter)) {
				computeSuccsInternal(state, letter);
			}
		}
		return m_Result.internalSuccessors(state, letter);
	}


	/**
	 * Have the internal successors of state and letter already been computed.
	 */
	protected abstract boolean areInternalSuccsComputed(IPredicate state, CodeBlock letter);


	protected abstract void computeSuccsInternal(IPredicate state, CodeBlock letter);


	@Override
	public final Iterable<OutgoingInternalTransition<CodeBlock, IPredicate>> internalSuccessors(
			IPredicate state) {
		if (!m_ComputationFinished) {
			for (CodeBlock letter : lettersInternal(state)) {
				if (!areInternalSuccsComputed(state, letter)) {
					computeSuccsInternal(state, letter);
				}
			}
		}
		return m_Result.internalSuccessors(state);
	}

	@Override
	public final Iterable<OutgoingCallTransition<CodeBlock, IPredicate>> callSuccessors(
			IPredicate state, CodeBlock letter) {
		Call call = (Call) letter;
		if (!m_ComputationFinished) {
			if (!areCallSuccsComputed(state, call)) {
				computeSuccsCall(state, call);
			}
		}
		return m_Result.callSuccessors(state, call);
	}
	
	/**
	 * Have the call successors of state and call already been computed.
	 */
	protected abstract boolean areCallSuccsComputed(IPredicate state, Call call);

	protected abstract void computeSuccsCall(IPredicate state, Call call);


	@Override
	public final Iterable<OutgoingCallTransition<CodeBlock, IPredicate>> callSuccessors(
			IPredicate state) {
		if (!m_ComputationFinished) {
			for (CodeBlock letter : lettersCall(state)) {
				Call call = (Call) letter;
				if (!m_Result.callSuccessors(state, call).iterator().hasNext()) {
					computeSuccsCall(state, call);
				}
			}
		}
		return m_Result.callSuccessors(state);
	}

	@Override
	public final Iterable<OutgoingReturnTransition<CodeBlock, IPredicate>> returnSucccessors(
			IPredicate state, IPredicate hier, CodeBlock letter) {
		Return ret = (Return) letter;
		if (!m_ComputationFinished) {
			if (!areReturnSuccsComputed(state, hier, ret)) {
				computeSuccsReturn(state, hier, ret);
			}
		}
		return m_Result.returnSucccessors(state, hier, ret);
	}

	/**
	 * Have the return successors of state, hier and ret already been computed.
	 */
	protected abstract boolean areReturnSuccsComputed(IPredicate state, IPredicate hier, Return ret);


	protected abstract void computeSuccsReturn(IPredicate state, IPredicate hier, Return ret);


	@Override
	public final Iterable<OutgoingReturnTransition<CodeBlock, IPredicate>> returnSuccessorsGivenHier(
			IPredicate state, IPredicate hier) {
		if (!m_ComputationFinished) {
			for (CodeBlock letter : lettersReturn(state)) {
				Return ret = (Return) letter;
				if (!m_Result.returnSucccessors(state, hier, ret).iterator().hasNext()) {
					computeSuccsReturn(state, hier, ret);
				}
			}
		}
		return m_Result.returnSuccessorsGivenHier(state, hier);
	}
	
	

	
	
	@Override
	public final String toString() {
		if (m_ComputationFinished) {
			return (new AtsDefinitionPrinter<String,String>("nwa", this)).getDefinitionAsString();
		} else {
			return "automaton under construction";
		}
	}

}
