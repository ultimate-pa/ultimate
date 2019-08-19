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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NwaCacheBookkeeping;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;

/**
 * Superclass for interpolant automata that are build on-demand. An interpolant automaton is an automaton
 * <ul>
 * <li>whose letters are LETTERs
 * <li>whose states are IPredicates
 * <li>whose accepting state is an IPredicate whose formula is "false"
 * <li>that has a transition (ψ, st, φ) only if the Hoare triple {ψ} st {φ} is valid.
 * </ul>
 *
 * The on-demand construction works as follows. Initially, the automaton does not have any transitions. Furthermore, the
 * automaton is always in one of the following two modes Mode.ON_DEMAND_CONSTRUCTION or Mode.READ_ONLY. The user can
 * switch between both modes using the {@code #switchToOnDemandConstructionMode()} and the
 * {@code #switchToReadonlyMode()} methods. New transitions are only added if the automaton is in ON_DEMAND_CONSTRUCTION
 * mode. Furthermore, new transitions are only added on-demand while the user asks the for successors (e.g., via the
 * {@code #internalSuccessors(IPredicate)} method. If the automaton is asked for successors of a given state ψ, the
 * automaton first checks if outgoing transitions for this state were already constructed(
 * {@code #mAlreadyConstrucedAutomaton}). If these were already constructed, these successors are returned. Otherwise
 * the successors are constructed and then returned. The construction of successor is defined by the subclasses of this
 * class. Note that while constructing successor transitions new states may be added. In the construction of successors
 * information from the automaton {@code #mInputInterpolantAutomaton} can be used.
 *
 * @author Matthias Heizmann
 *
 */
public abstract class AbstractInterpolantAutomaton<LETTER>
		implements INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> {

	public enum Mode {
		ON_DEMAND_CONSTRUCTION, READ_ONLY
	}

	protected final IUltimateServiceProvider mServices;
	protected final ILogger mLogger;

	protected final CfgSmtToolkit mCsToolkit;
	protected final IHoareTripleChecker mIHoareTripleChecker;
	protected final IPredicate mIaFalseState;
	protected final NestedWordAutomatonCache<LETTER, IPredicate> mAlreadyConstructedAutomaton;
	protected final INestedWordAutomaton<LETTER, IPredicate> mInputInterpolantAutomaton;

	private Mode mMode = Mode.ON_DEMAND_CONSTRUCTION;

	private final InternalSuccessorComputationHelper mInSucComp;
	private final CallSuccessorComputationHelper mCaSucComp;
	private final ReturnSuccessorComputationHelper mReSucComp;
	private final ISuccessorComputationBookkeeping<LETTER> mSuccessorComputationBookkeeping;

	/**
	 * @param useEfficientTotalAutomatonBookkeeping
	 *            If the constructed automaton is guaranteed to be we use a more efficient bookkeeping for already
	 *            computed successors.
	 */
	public AbstractInterpolantAutomaton(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final IHoareTripleChecker hoareTripleChecker, final boolean useEfficientTotalAutomatonBookkeeping,
			final IPredicate falseState, final INestedWordAutomaton<LETTER, IPredicate> inputInterpolantAutomaton) {
		super();
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mCsToolkit = csToolkit;
		mIHoareTripleChecker = hoareTripleChecker;
		mIaFalseState = falseState;
		mInputInterpolantAutomaton = inputInterpolantAutomaton;
		mInSucComp = new InternalSuccessorComputationHelper();
		mCaSucComp = new CallSuccessorComputationHelper();
		mReSucComp = new ReturnSuccessorComputationHelper();
		mAlreadyConstructedAutomaton = new NestedWordAutomatonCache<>(new AutomataLibraryServices(mServices),
				inputInterpolantAutomaton.getVpAlphabet(),
				(IEmptyStackStateFactory<IPredicate>) inputInterpolantAutomaton.getStateFactory());
		if (useEfficientTotalAutomatonBookkeeping) {
			mSuccessorComputationBookkeeping = new SuccessorComputationBookkeepingForTotalAutomata();
		} else {
			mSuccessorComputationBookkeeping = new DefaultSuccessorComputationBookkeeping();
		}
	}

	/**
	 * Switch the mode to READ_ONLY. In this mode the automaton returns only existing transitions but does not compute
	 * new ones.
	 */
	public final void switchToReadonlyMode() {
		if (mMode == Mode.READ_ONLY) {
			throw new AssertionError("already in mode READ_ONLY");
		}
		mMode = Mode.READ_ONLY;
		mIHoareTripleChecker.releaseLock();
		mLogger.info(switchToReadonlyMessage());
	}

	/**
	 * Switch the mode to ON_DEMAND_CONSTRUCTION. In this mode the automaton behaves as follows: If the automaton is
	 * asked if a transition exists, the automaton checks the rules that define this automaton (validity of Hoare
	 * triples) and constructs the transition on demand.
	 */
	public final void switchToOnDemandConstructionMode() {
		if (mMode == Mode.ON_DEMAND_CONSTRUCTION) {
			throw new AssertionError("already in mode ON_DEMAND_CONSTRUCTION");
		}
		mMode = Mode.ON_DEMAND_CONSTRUCTION;
		mLogger.info(switchToOnDemandConstructionMessage());
	}

	protected abstract String startMessage();

	protected abstract String switchToReadonlyMessage();

	protected abstract String switchToOnDemandConstructionMessage();

	protected abstract void computeSuccs(IPredicate state, IPredicate hier, LETTER ret, SuccessorComputationHelper sch);

	@Override
	public final int size() {
		return mAlreadyConstructedAutomaton.size();
	}

	@Override
	public final Set<LETTER> getAlphabet() {
		return mAlreadyConstructedAutomaton.getAlphabet();
	}

	@Override
	public final String sizeInformation() {
		if (mInputInterpolantAutomaton == null) {
			return "yet neither states nor transitions";
		}
		return mInputInterpolantAutomaton.sizeInformation();
	}

	@Override
	public VpAlphabet<LETTER> getVpAlphabet() {
		return mAlreadyConstructedAutomaton.getVpAlphabet();
	}

	@Override
	public final IStateFactory<IPredicate> getStateFactory() {
		return mAlreadyConstructedAutomaton.getStateFactory();
	}

	@Override
	public final IPredicate getEmptyStackState() {
		return mAlreadyConstructedAutomaton.getEmptyStackState();
	}

	@Override
	public final Iterable<IPredicate> getInitialStates() {
		return mAlreadyConstructedAutomaton.getInitialStates();
	}

	@Override
	public final boolean isInitial(final IPredicate state) {
		return mAlreadyConstructedAutomaton.isInitial(state);
	}

	@Override
	public final boolean isFinal(final IPredicate state) {
		return mAlreadyConstructedAutomaton.isFinal(state);
	}

	@Override
	public final Set<LETTER> lettersInternal(final IPredicate state) {
		return getVpAlphabet().getInternalAlphabet();
	}

	@Override
	public final Set<LETTER> lettersCall(final IPredicate state) {
		return getVpAlphabet().getCallAlphabet();
	}

	@Override
	public final Set<LETTER> lettersReturn(final IPredicate state, final IPredicate hier) {
		return getVpAlphabet().getReturnAlphabet();
	}

	@Override
	public final Iterable<OutgoingInternalTransition<LETTER, IPredicate>> internalSuccessors(final IPredicate state,
			final LETTER letter) {
		if (mMode == Mode.ON_DEMAND_CONSTRUCTION) {
			if (!mSuccessorComputationBookkeeping.areInternalSuccsComputed(state, letter)) {
				computeSuccs(state, null, letter, mInSucComp);
			}
		}
		return mAlreadyConstructedAutomaton.internalSuccessors(state, letter);
	}

	@Override
	public final Iterable<OutgoingInternalTransition<LETTER, IPredicate>> internalSuccessors(final IPredicate state) {
		if (mMode == Mode.ON_DEMAND_CONSTRUCTION) {
			for (final LETTER letter : lettersInternal(state)) {
				if (!mSuccessorComputationBookkeeping.areInternalSuccsComputed(state, letter)) {
					computeSuccs(state, null, letter, mInSucComp);
				}
			}
		}
		return mAlreadyConstructedAutomaton.internalSuccessors(state);
	}

	@Override
	public final Iterable<OutgoingCallTransition<LETTER, IPredicate>> callSuccessors(final IPredicate state,
			final LETTER letter) {
		if (mMode == Mode.ON_DEMAND_CONSTRUCTION) {
			if (!mSuccessorComputationBookkeeping.areCallSuccsComputed(state, letter)) {
				computeSuccs(state, null, letter, mCaSucComp);
			}
		}
		return mAlreadyConstructedAutomaton.callSuccessors(state, letter);
	}

	@Override
	public final Iterable<OutgoingCallTransition<LETTER, IPredicate>> callSuccessors(final IPredicate state) {
		if (mMode == Mode.ON_DEMAND_CONSTRUCTION) {
			for (final LETTER letter : lettersCall(state)) {
				if (!mAlreadyConstructedAutomaton.callSuccessors(state, letter).iterator().hasNext()) {
					computeSuccs(state, null, letter, mCaSucComp);
				}
			}
		}
		return mAlreadyConstructedAutomaton.callSuccessors(state);
	}

	@Override
	public final Iterable<OutgoingReturnTransition<LETTER, IPredicate>> returnSuccessors(final IPredicate state,
			final IPredicate hier, final LETTER letter) {
		if (mMode == Mode.ON_DEMAND_CONSTRUCTION) {
			if (!mSuccessorComputationBookkeeping.areReturnSuccsComputed(state, hier, letter)) {
				computeSuccs(state, hier, letter, mReSucComp);
			}
		}
		return mAlreadyConstructedAutomaton.returnSuccessors(state, hier, letter);
	}

	@Override
	public final Iterable<OutgoingReturnTransition<LETTER, IPredicate>>
			returnSuccessorsGivenHier(final IPredicate state, final IPredicate hier) {
		if (mMode == Mode.ON_DEMAND_CONSTRUCTION) {
			for (final LETTER letter : lettersReturn(state, hier)) {
				if (!mAlreadyConstructedAutomaton.returnSuccessors(state, hier, letter).iterator().hasNext()) {
					computeSuccs(state, hier, letter, mReSucComp);
				}
			}
		}
		return mAlreadyConstructedAutomaton.returnSuccessorsGivenHier(state, hier);
	}

	@Override
	public final String toString() {
		if (mMode == Mode.READ_ONLY) {
			return new AutomatonDefinitionPrinter<String, String>(new AutomataLibraryServices(mServices), "nwa",
					Format.ATS, this).getDefinitionAsString();
		}
		return "automaton under construction";
	}

	public int computeNumberOfInternalTransitions() {
		return mAlreadyConstructedAutomaton.computeNumberOfInternalTransitions();
	}

	/**
	 * Abstract class for successor computation. Subclasses are the successor computations for internal, call, and
	 * return. Because we can only override methods with the same signature (in Java) we use the 3-parameter-signature
	 * for return (with hierarchical state) and use null as hierarchical state for call and internal.
	 */
	public abstract class SuccessorComputationHelper {

		public abstract boolean isLinearPredecessorFalse(IPredicate resPred);

		public abstract boolean isHierarchicalPredecessorFalse(IPredicate resPred);

		public abstract void addTransition(IPredicate resPred, IPredicate resHier, LETTER letter, IPredicate resSucc);

		public abstract Validity computeSuccWithSolver(IPredicate resPred, IPredicate resHier, LETTER letter,
				IPredicate resSucc);

		public abstract Collection<IPredicate> getSuccsInterpolantAutomaton(IPredicate resPred, IPredicate resHier,
				LETTER letter);

		public abstract void reportSuccsComputed(IPredicate resPred, IPredicate resHier, LETTER letter);

	}

	protected class InternalSuccessorComputationHelper extends SuccessorComputationHelper {

		@Override
		public boolean isLinearPredecessorFalse(final IPredicate resPred) {
			return resPred == mIaFalseState;
		}

		@Override
		public boolean isHierarchicalPredecessorFalse(final IPredicate resHier) {
			assert resHier == null;
			return false;
		}

		@Override
		public void addTransition(final IPredicate resPred, final IPredicate resHier, final LETTER letter,
				final IPredicate inputSucc) {
			assert resHier == null;
			mAlreadyConstructedAutomaton.addInternalTransition(resPred, letter, inputSucc);
		}

		@Override
		public Validity computeSuccWithSolver(final IPredicate resPred, final IPredicate resHier, final LETTER letter,
				final IPredicate inputSucc) {
			assert resHier == null;
			return mIHoareTripleChecker.checkInternal(resPred, (IInternalAction) letter, inputSucc);
		}

		@Override
		public Collection<IPredicate> getSuccsInterpolantAutomaton(final IPredicate resPred, final IPredicate resHier,
				final LETTER letter) {
			assert resHier == null;
			final Collection<IPredicate> succs =
					NestedWordAutomataUtils.constructInternalSuccessors(mInputInterpolantAutomaton, resPred, letter);
			return succs;
		}

		@Override
		public void reportSuccsComputed(final IPredicate resPred, final IPredicate resHier, final LETTER letter) {
			assert resHier == null;
			mSuccessorComputationBookkeeping.reportInternalSuccsComputed(resPred, letter);
		}

	}

	protected class CallSuccessorComputationHelper extends SuccessorComputationHelper {

		@Override
		public boolean isLinearPredecessorFalse(final IPredicate resPred) {
			return resPred == mIaFalseState;
		}

		@Override
		public boolean isHierarchicalPredecessorFalse(final IPredicate resHier) {
			assert resHier == null;
			return false;
		}

		@Override
		public void addTransition(final IPredicate resPred, final IPredicate resHier, final LETTER letter,
				final IPredicate inputSucc) {
			assert resHier == null;
			mAlreadyConstructedAutomaton.addCallTransition(resPred, letter, inputSucc);
		}

		@Override
		public Validity computeSuccWithSolver(final IPredicate resPred, final IPredicate resHier, final LETTER letter,
				final IPredicate inputSucc) {
			assert resHier == null;
			return mIHoareTripleChecker.checkCall(resPred, (ICallAction) letter, inputSucc);
		}

		@Override
		public Collection<IPredicate> getSuccsInterpolantAutomaton(final IPredicate resPred, final IPredicate resHier,
				final LETTER letter) {
			assert resHier == null;
			final Collection<IPredicate> succs =
					NestedWordAutomataUtils.constructCallSuccessors(mInputInterpolantAutomaton, resPred, letter);
			return succs;
		}

		@Override
		public void reportSuccsComputed(final IPredicate resPred, final IPredicate resHier, final LETTER letter) {
			assert resHier == null;
			mSuccessorComputationBookkeeping.reportCallSuccsComputed(resPred, letter);
		}

	}

	public class ReturnSuccessorComputationHelper extends SuccessorComputationHelper {

		@Override
		public boolean isLinearPredecessorFalse(final IPredicate resPred) {
			return resPred == mIaFalseState;
		}

		@Override
		public boolean isHierarchicalPredecessorFalse(final IPredicate resHier) {
			return resHier == mIaFalseState;
		}

		@Override
		public void addTransition(final IPredicate resPred, final IPredicate resHier, final LETTER letter,
				final IPredicate inputSucc) {
			mAlreadyConstructedAutomaton.addReturnTransition(resPred, resHier, letter, inputSucc);
		}

		@Override
		public Validity computeSuccWithSolver(final IPredicate resPred, final IPredicate resHier, final LETTER letter,
				final IPredicate inputSucc) {
			return mIHoareTripleChecker.checkReturn(resPred, resHier, (IReturnAction) letter, inputSucc);
		}

		@Override
		public Collection<IPredicate> getSuccsInterpolantAutomaton(final IPredicate resPred, final IPredicate resHier,
				final LETTER letter) {
			final Collection<IPredicate> succs = NestedWordAutomataUtils
					.constructReturnSuccessors(mInputInterpolantAutomaton, resPred, resHier, letter);
			return succs;
		}

		@Override
		public void reportSuccsComputed(final IPredicate resPred, final IPredicate resHier, final LETTER letter) {
			mSuccessorComputationBookkeeping.reportReturnSuccsComputed(resPred, resHier, letter);
		}

	}

	/**
	 * Objects that implement this interface provide information if successors have already been computed.
	 *
	 * @author Matthias Heizmann
	 */
	public interface ISuccessorComputationBookkeeping<LETTER> {

		/**
		 * Have the internal successors of state and letter already been computed.
		 */
		boolean areInternalSuccsComputed(IPredicate state, LETTER letter);

		/**
		 * Announce that the internal successors of state and letter have been computed.
		 */
		void reportInternalSuccsComputed(IPredicate state, LETTER letter);

		/**
		 * Have the call successors of state and call already been computed.
		 */
		boolean areCallSuccsComputed(IPredicate state, LETTER call);

		/**
		 * Announce that the call successors of state and call have been computed.
		 */
		void reportCallSuccsComputed(IPredicate state, LETTER call);

		/**
		 * Have the return successors of state, hier and ret already been computed.
		 */
		boolean areReturnSuccsComputed(IPredicate state, IPredicate hier, LETTER ret);

		/**
		 * Announce that the return successors of state, hier and have been computed.
		 */
		void reportReturnSuccsComputed(IPredicate state, IPredicate hier, LETTER ret);
	}

	/**
	 * Default implementation of {@link ISuccessorComputationBookkeeping} uses a NwaCacheBookkeeping to store which
	 * successors have already been computed.
	 */
	private class DefaultSuccessorComputationBookkeeping implements ISuccessorComputationBookkeeping<LETTER> {

		private final NwaCacheBookkeeping<LETTER, IPredicate> mResultBookkeeping = new NwaCacheBookkeeping<>();

		@Override
		public boolean areInternalSuccsComputed(final IPredicate state, final LETTER letter) {
			return mResultBookkeeping.isCachedInternal(state, letter);
		}

		@Override
		public void reportInternalSuccsComputed(final IPredicate state, final LETTER letter) {
			mResultBookkeeping.reportCachedInternal(state, letter);
		}

		@Override
		public boolean areCallSuccsComputed(final IPredicate state, final LETTER call) {
			return mResultBookkeeping.isCachedCall(state, call);
		}

		@Override
		public void reportCallSuccsComputed(final IPredicate state, final LETTER call) {
			mResultBookkeeping.reportCachedCall(state, call);
		}

		@Override
		public boolean areReturnSuccsComputed(final IPredicate state, final IPredicate hier, final LETTER ret) {
			return mResultBookkeeping.isCachedReturn(state, hier, ret);
		}

		@Override
		public void reportReturnSuccsComputed(final IPredicate state, final IPredicate hier, final LETTER ret) {
			mResultBookkeeping.reportCachedReturn(state, hier, ret);
		}

	}

	/**
	 * Implementation of {@link ISuccessorComputationBookkeeping} that avoids an additional bookkeeping but works only
	 * if we construct a total automata. Idea: If there is no successor, we have not yet computed the successors,
	 * because there would be at least one since the automaton is total. (An automaton is total if for each state and
	 * each letter, there is at least one outgoing transition)
	 */
	private class SuccessorComputationBookkeepingForTotalAutomata implements ISuccessorComputationBookkeeping<LETTER> {

		@Override
		public boolean areInternalSuccsComputed(final IPredicate state, final LETTER letter) {
			final Collection<IPredicate> succs = mAlreadyConstructedAutomaton.succInternal(state, letter);
			return succs.iterator().hasNext();
		}

		@Override
		public boolean areCallSuccsComputed(final IPredicate state, final LETTER call) {
			final Collection<IPredicate> succs = mAlreadyConstructedAutomaton.succCall(state, call);
			return succs.iterator().hasNext();
		}

		@Override
		public boolean areReturnSuccsComputed(final IPredicate state, final IPredicate hier, final LETTER ret) {
			final Collection<IPredicate> succs = mAlreadyConstructedAutomaton.succReturn(state, hier, ret);
			return succs.iterator().hasNext();
		}

		@Override
		public void reportInternalSuccsComputed(final IPredicate state, final LETTER letter) {
			// do nothing, information is implicitly stored in total automaton
		}

		@Override
		public void reportCallSuccsComputed(final IPredicate state, final LETTER call) {
			// do nothing, information is implicitly stored in total automaton
		}

		@Override
		public void reportReturnSuccsComputed(final IPredicate state, final IPredicate hier, final LETTER ret) {
			// do nothing, information is implicitly stored in total automaton
		}

	}

}
