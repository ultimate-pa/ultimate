/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender;

import java.util.Collection;
import java.util.Collections;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomatonCache;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NwaCacheBookkeeping;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

/**
 * Superclass for interpolant automata that are build on-demand.
 * An interpolant automaton is an automaton
 * <ul>
 * <li> whose letters are CodeBlocks
 * <li> whose states are IPredicates
 * <li> whose accepting state is an IPredicate whose formula is "false"
 * <li> that has a transition (ψ, st, φ) only if the Hoare triple {ψ} st {φ}
 *  is valid.
 * </ul>
 *  
 *  The on-demand construction works as follows.
 *  Initially, the automaton does not have any transitions. Furthermore,
 *  the automaton is always in one of the following two modes 
 *  Mode.ON_DEMAND_CONSTRUCTION or Mode.READ_ONLY.
 *  The user can switch between both modes using the 
 *  {@code #switchToOnDemandConstructionMode()} and the 
 *  {@code #switchToReadonlyMode()} methods.
 *  New transitions are only added if the automaton is in 
 *  ON_DEMAND_CONSTRUCTION mode. Furthermore, 
 *  new transitions are only added on-demand while the user asks the for 
 *  successors (e.g., via the {@code #internalSuccessors(IPredicate)} method.
 *  If the automaton is asked for successors of a given state ψ, the automaton
 *  first checks if outgoing transitions for this state were already 
 *  constructed({@code #m_AlreadyConstrucedAutomaton}).
 *  If these were already constructed, these successors are returned.
 *  Otherwise the successors are constructed and then returned.
 *  The construction of successor is defined by the subclasses of this class.
 *  Note that while constructing successor transitions new states may be added.
 *  In the construction of successors information from the automaton 
 *  {@code #m_InputInterpolantAutomaton} can be used.
 *  
 * @author Matthias Heizmann
 * 
 */
public abstract class AbstractInterpolantAutomaton implements INestedWordAutomatonSimple<CodeBlock, IPredicate> {
	
	public enum Mode { ON_DEMAND_CONSTRUCTION, READ_ONLY }

	protected final IUltimateServiceProvider m_Services;
	protected final Logger mLogger;

	protected final SmtManager m_SmtManager;
	protected final IHoareTripleChecker m_IHoareTripleChecker;
	protected final IPredicate m_IaFalseState;
	protected final NestedWordAutomatonCache<CodeBlock, IPredicate> m_AlreadyConstrucedAutomaton;
	protected final NestedWordAutomaton<CodeBlock, IPredicate> m_InputInterpolantAutomaton;
	
	private Mode m_Mode = Mode.ON_DEMAND_CONSTRUCTION;

	private final InternalSuccessorComputationHelper m_InSucComp;
	private final CallSuccessorComputationHelper m_CaSucComp;
	private final ReturnSuccessorComputationHelper m_ReSucComp;
	private final ISuccessorComputationBookkeeping m_SuccessorComputationBookkeeping;
	

	/**
	 * @param useEfficientTotalAutomatonBookkeeping If the constructed automaton
	 * is guaranteed to be we use a more efficient bookkeeping for
	 * already computed successors. 
	 */
	public AbstractInterpolantAutomaton(IUltimateServiceProvider services, 
			SmtManager smtManager, IHoareTripleChecker hoareTripleChecker,
			boolean useEfficientTotalAutomatonBookkeeping,
			INestedWordAutomaton<CodeBlock, IPredicate> abstraction, IPredicate falseState,
			NestedWordAutomaton<CodeBlock, IPredicate> interpolantAutomaton, Logger logger) {
		super();
		m_Services = services;
		mLogger = logger;
		m_SmtManager = smtManager;
		m_IHoareTripleChecker = hoareTripleChecker;
		m_IaFalseState = falseState;
		m_InputInterpolantAutomaton = interpolantAutomaton;
		m_InSucComp = new InternalSuccessorComputationHelper();
		m_CaSucComp = new CallSuccessorComputationHelper();
		m_ReSucComp = new ReturnSuccessorComputationHelper();
		m_AlreadyConstrucedAutomaton = new NestedWordAutomatonCache<CodeBlock, IPredicate>(m_Services, abstraction.getInternalAlphabet(),
				abstraction.getCallAlphabet(), abstraction.getReturnAlphabet(), abstraction.getStateFactory());
		if (useEfficientTotalAutomatonBookkeeping) {
			m_SuccessorComputationBookkeeping = new SuccessorComputationBookkeepingForTotalAutomata();
		} else {
			m_SuccessorComputationBookkeeping = new DefaultSuccessorComputationBookkeeping();
		}
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
			m_IHoareTripleChecker.releaseLock();
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
		return m_AlreadyConstrucedAutomaton.size();
	}

	@Override
	public final Set<CodeBlock> getAlphabet() {
		return m_AlreadyConstrucedAutomaton.getAlphabet();
	}

	@Override
	public final String sizeInformation() {
		return m_AlreadyConstrucedAutomaton.sizeInformation();
	}

	@Override
	public final Set<CodeBlock> getInternalAlphabet() {
		return m_AlreadyConstrucedAutomaton.getInternalAlphabet();
	}

	@Override
	public final Set<CodeBlock> getCallAlphabet() {
		return m_AlreadyConstrucedAutomaton.getCallAlphabet();
	}

	@Override
	public final Set<CodeBlock> getReturnAlphabet() {
		return m_AlreadyConstrucedAutomaton.getReturnAlphabet();
	}

	@Override
	public final StateFactory<IPredicate> getStateFactory() {
		return m_AlreadyConstrucedAutomaton.getStateFactory();
	}

	@Override
	public final IPredicate getEmptyStackState() {
		return m_AlreadyConstrucedAutomaton.getEmptyStackState();
	}

	@Override
	public final Iterable<IPredicate> getInitialStates() {
		return m_AlreadyConstrucedAutomaton.getInitialStates();
	}

	@Override
	public final boolean isInitial(IPredicate state) {
		return m_AlreadyConstrucedAutomaton.isInitial(state);
	}

	@Override
	public final boolean isFinal(IPredicate state) {
		return m_AlreadyConstrucedAutomaton.isFinal(state);
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
			if (!m_SuccessorComputationBookkeeping.areInternalSuccsComputed(state, letter)) {
				computeSuccs(state, null, letter, m_InSucComp);
			}
		}
		return m_AlreadyConstrucedAutomaton.internalSuccessors(state, letter);
	}

	protected abstract void computeSuccs(IPredicate state, IPredicate hier, CodeBlock ret,
			SuccessorComputationHelper sch);


	@Override
	public final Iterable<OutgoingInternalTransition<CodeBlock, IPredicate>> internalSuccessors(IPredicate state) {
		if (m_Mode == Mode.ON_DEMAND_CONSTRUCTION) {
			for (CodeBlock letter : lettersInternal(state)) {
				if (!m_SuccessorComputationBookkeeping.areInternalSuccsComputed(state, letter)) {
					computeSuccs(state, null, letter, m_InSucComp);
				}
			}
		}
		return m_AlreadyConstrucedAutomaton.internalSuccessors(state);
	}

	@Override
	public final Iterable<OutgoingCallTransition<CodeBlock, IPredicate>> callSuccessors(IPredicate state,
			CodeBlock letter) {
		Call call = (Call) letter;
		if (m_Mode == Mode.ON_DEMAND_CONSTRUCTION) {
			if (!m_SuccessorComputationBookkeeping.areCallSuccsComputed(state, call)) {
				computeSuccs(state, null, letter, m_CaSucComp);
			}
		}
		return m_AlreadyConstrucedAutomaton.callSuccessors(state, call);
	}



	@Override
	public final Iterable<OutgoingCallTransition<CodeBlock, IPredicate>> callSuccessors(IPredicate state) {
		if (m_Mode == Mode.ON_DEMAND_CONSTRUCTION) {
			for (CodeBlock letter : lettersCall(state)) {
				Call call = (Call) letter;
				if (!m_AlreadyConstrucedAutomaton.callSuccessors(state, call).iterator().hasNext()) {
					computeSuccs(state, null, letter, m_CaSucComp);
				}
			}
		}
		return m_AlreadyConstrucedAutomaton.callSuccessors(state);
	}

	@Override
	public final Iterable<OutgoingReturnTransition<CodeBlock, IPredicate>> returnSucccessors(IPredicate state,
			IPredicate hier, CodeBlock letter) {
		Return ret = (Return) letter;
		if (m_Mode == Mode.ON_DEMAND_CONSTRUCTION) {
			if (!m_SuccessorComputationBookkeeping.areReturnSuccsComputed(state, hier, ret)) {
				computeSuccs(state, hier, letter, m_ReSucComp);
			}
		}
		return m_AlreadyConstrucedAutomaton.returnSucccessors(state, hier, ret);
	}



	@Override
	public final Iterable<OutgoingReturnTransition<CodeBlock, IPredicate>> returnSuccessorsGivenHier(IPredicate state,
			IPredicate hier) {
		if (m_Mode == Mode.ON_DEMAND_CONSTRUCTION) {
			for (CodeBlock letter : lettersReturn(state)) {
				Return ret = (Return) letter;
				if (!m_AlreadyConstrucedAutomaton.returnSucccessors(state, hier, ret).iterator().hasNext()) {
					computeSuccs(state, hier, letter, m_ReSucComp);
				}
			}
		}
		return m_AlreadyConstrucedAutomaton.returnSuccessorsGivenHier(state, hier);
	}

	@Override
	public final String toString() {
		if (m_Mode == Mode.READ_ONLY) {
			return (new AutomatonDefinitionPrinter<String, String>(m_Services, "nwa", Format.ATS, this)).getDefinitionAsString();
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
				IPredicate resSucc);

		public abstract Validity computeSuccWithSolver(IPredicate resPred, IPredicate resHier, CodeBlock letter,
				IPredicate resSucc);

		public abstract Collection<IPredicate> getSuccsInterpolantAutomaton(IPredicate resPred, IPredicate resHier,
				CodeBlock letter);
		
		public abstract void reportSuccsComputed(IPredicate resPred, IPredicate resHier, CodeBlock letter);

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
			m_AlreadyConstrucedAutomaton.addInternalTransition(resPred, letter, inputSucc);
		}

		@Override
		public Validity computeSuccWithSolver(IPredicate resPred, IPredicate resHier, CodeBlock letter,
				IPredicate inputSucc) {
			assert resHier == null;
			return m_IHoareTripleChecker.checkInternal(resPred, letter, inputSucc);
		}

		@Override
		public Collection<IPredicate> getSuccsInterpolantAutomaton(IPredicate resPred, IPredicate resHier,
				CodeBlock letter) {
			assert resHier == null;
			Collection<IPredicate> succs = m_InputInterpolantAutomaton.succInternal(resPred, letter);
			if (succs == null) {
				return Collections.emptySet();
			} else {
				return succs;
			}
		}

		@Override
		public void reportSuccsComputed(IPredicate resPred, IPredicate resHier,	CodeBlock letter) {
			assert resHier == null;
			m_SuccessorComputationBookkeeping.reportInternalSuccsComputed(resPred, letter);
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
			m_AlreadyConstrucedAutomaton.addCallTransition(resPred, letter, inputSucc);
		}

		@Override
		public Validity computeSuccWithSolver(IPredicate resPred, IPredicate resHier, CodeBlock letter,
				IPredicate inputSucc) {
			assert resHier == null;
			return m_IHoareTripleChecker.checkCall(resPred, letter, inputSucc);
		}

		@Override
		public Collection<IPredicate> getSuccsInterpolantAutomaton(IPredicate resPred, IPredicate resHier,
				CodeBlock letter) {
			assert resHier == null;
			Collection<IPredicate> succs = m_InputInterpolantAutomaton.succCall(resPred, letter);
			if (succs == null) {
				return Collections.emptySet();
			} else {
				return succs;
			}
		}

		@Override
		public void reportSuccsComputed(IPredicate resPred, IPredicate resHier,	CodeBlock letter) {
			assert resHier == null;
			m_SuccessorComputationBookkeeping.reportCallSuccsComputed(resPred, (Call) letter);
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
			m_AlreadyConstrucedAutomaton.addReturnTransition(resPred, resHier, letter, inputSucc);
		}

		@Override
		public Validity computeSuccWithSolver(IPredicate resPred, IPredicate resHier, CodeBlock letter,
				IPredicate inputSucc) {
			return m_IHoareTripleChecker.checkReturn(resPred, resHier, letter, inputSucc);
		}

		@Override
		public Collection<IPredicate> getSuccsInterpolantAutomaton(IPredicate resPred, IPredicate resHier,
				CodeBlock letter) {
			Collection<IPredicate> succs = m_InputInterpolantAutomaton.succReturn(resPred, resHier, letter);
			if (succs == null) {
				return Collections.emptySet();
			} else {
				return succs;
			}
		}

		@Override
		public void reportSuccsComputed(IPredicate resPred, IPredicate resHier,	CodeBlock letter) {
			m_SuccessorComputationBookkeeping.reportReturnSuccsComputed(resPred, resHier, (Return) letter);
		}

	}
	
	
	
	
	/**
	 * Objects that implement this interface provide information if successors
	 * have already been computed.
	 * 
	 * @author Matthias Heizmann
	 */
	public interface ISuccessorComputationBookkeeping {

		/**
		 * Have the internal successors of state and letter already been computed.
		 */
		abstract boolean areInternalSuccsComputed(IPredicate state, CodeBlock letter);
		
		/**
		 * Announce that the internal successors of state and letter have been computed.
		 */
		abstract void reportInternalSuccsComputed(IPredicate state, CodeBlock letter);
		
		/**
		 * Have the call successors of state and call already been computed.
		 */
		abstract boolean areCallSuccsComputed(IPredicate state, Call call);
		
		/**
		 * Announce that the call successors of state and call have been computed.
		 */
		abstract void reportCallSuccsComputed(IPredicate state, Call call);
		
		/**
		 * Have the return successors of state, hier and ret already been computed.
		 */
		abstract boolean areReturnSuccsComputed(IPredicate state, IPredicate hier, Return ret);

		/**
		 * Announce that the return successors of state, hier and have been computed.
		 */
		abstract void reportReturnSuccsComputed(IPredicate state, IPredicate hier,
				Return ret);
	}
	
	/**
	 * Default implementation of {@link ISuccessorComputationBookkeeping} uses
	 * a NwaCacheBookkeeping to store which successors have already been computed.
	 */
	private class DefaultSuccessorComputationBookkeeping implements	ISuccessorComputationBookkeeping {

		private final NwaCacheBookkeeping<CodeBlock, IPredicate> m_ResultBookkeeping = 
				new NwaCacheBookkeeping<CodeBlock, IPredicate>();

		@Override
		public boolean areInternalSuccsComputed(IPredicate state, CodeBlock letter) {
			return m_ResultBookkeeping.isCachedInternal(state, letter);
		}
		
		@Override
		public void reportInternalSuccsComputed(IPredicate state, CodeBlock letter) {
			m_ResultBookkeeping.reportCachedInternal(state, letter);
		}


		@Override
		public boolean areCallSuccsComputed(IPredicate state, Call call) {
			return m_ResultBookkeeping.isCachedCall(state, call);
		}
		
		@Override
		public void reportCallSuccsComputed(IPredicate state, Call call) {
			m_ResultBookkeeping.reportCachedCall(state, call);
		}


		@Override
		public boolean areReturnSuccsComputed(IPredicate state, IPredicate hier, Return ret) {
			return m_ResultBookkeeping.isCachedReturn(state, hier, ret);
		}
		
		@Override
		public void reportReturnSuccsComputed(IPredicate state, IPredicate hier, Return ret) {
			m_ResultBookkeeping.reportCachedReturn(state, hier, ret);
		}

	}
	
	
	
	/**
	 * Implementation of {@link ISuccessorComputationBookkeeping} that avoids
	 * an additional bookkeeping but works only if we construct a total automata.
	 * Idea: If there is no successor, we have not yet computed the successors,
	 * because there would be at least one since the automaton is total.
	 * (An automaton is total if for each state and each letter, there is at least
	 * one outgoing transition)
	 */
	private class SuccessorComputationBookkeepingForTotalAutomata implements ISuccessorComputationBookkeeping {

		@Override
		public boolean areInternalSuccsComputed(IPredicate state, CodeBlock letter) {
			Collection<IPredicate> succs = m_AlreadyConstrucedAutomaton.succInternal(state, letter);
			if (succs == null) {
				return false;
			} else {
				return succs.iterator().hasNext();
			}
		}

		@Override
		public boolean areCallSuccsComputed(IPredicate state, Call call) {
			Collection<IPredicate> succs = m_AlreadyConstrucedAutomaton.succCall(state, call);
			if (succs == null) {
				return false;
			} else {
				return succs.iterator().hasNext();
			}
		}

		@Override
		public boolean areReturnSuccsComputed(IPredicate state, IPredicate hier,
				Return ret) {
			Collection<IPredicate> succs = m_AlreadyConstrucedAutomaton.succReturn(state, hier, ret);
			if (succs == null) {
				return false;
			} else {
				return succs.iterator().hasNext();
			}
		}

		@Override
		public void reportInternalSuccsComputed(IPredicate state, CodeBlock letter) {
			// do nothing, information is implicitly stored in total automaton
		}

		@Override
		public void reportCallSuccsComputed(IPredicate state, Call call) {
			// do nothing, information is implicitly stored in total automaton
		}

		@Override
		public void reportReturnSuccsComputed(IPredicate state,	IPredicate hier, Return ret) {
			// do nothing, information is implicitly stored in total automaton
		}

	}
	

}
