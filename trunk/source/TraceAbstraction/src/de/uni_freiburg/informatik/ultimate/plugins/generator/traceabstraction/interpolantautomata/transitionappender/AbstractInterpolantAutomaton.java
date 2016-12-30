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
import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NwaCacheBookkeeping;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;

/**
 * Superclass for interpolant automata that are build on-demand. An interpolant automaton is an automaton
 * <ul>
 * <li>whose letters are CodeBlocks
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
public abstract class AbstractInterpolantAutomaton implements INestedWordAutomatonSimple<CodeBlock, IPredicate> {

	public enum Mode {
		ON_DEMAND_CONSTRUCTION, READ_ONLY
	}

	protected final IUltimateServiceProvider mServices;
	protected final ILogger mLogger;

	protected final CfgSmtToolkit mCsToolkit;
	protected final IHoareTripleChecker mIHoareTripleChecker;
	protected final IPredicate mIaFalseState;
	protected final NestedWordAutomatonCache<CodeBlock, IPredicate> mAlreadyConstrucedAutomaton;
	protected final INestedWordAutomaton<CodeBlock, IPredicate> mInputInterpolantAutomaton;

	private Mode mMode = Mode.ON_DEMAND_CONSTRUCTION;

	private final InternalSuccessorComputationHelper mInSucComp;
	private final CallSuccessorComputationHelper mCaSucComp;
	private final ReturnSuccessorComputationHelper mReSucComp;
	private final ISuccessorComputationBookkeeping mSuccessorComputationBookkeeping;

	/**
	 * @param useEfficientTotalAutomatonBookkeeping
	 *            If the constructed automaton is guaranteed to be we use a more efficient bookkeeping for already
	 *            computed successors.
	 */
	public AbstractInterpolantAutomaton(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final IHoareTripleChecker hoareTripleChecker, final boolean useEfficientTotalAutomatonBookkeeping,
			final IPredicate falseState, final INestedWordAutomaton<CodeBlock, IPredicate> inputInterpolantAutomaton) {
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
		mAlreadyConstrucedAutomaton = new NestedWordAutomatonCache<>(new AutomataLibraryServices(mServices),
				inputInterpolantAutomaton.getInternalAlphabet(), inputInterpolantAutomaton.getCallAlphabet(), inputInterpolantAutomaton.getReturnAlphabet(),
				inputInterpolantAutomaton.getStateFactory());
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

	protected abstract void computeSuccs(IPredicate state, IPredicate hier, CodeBlock ret,
			SuccessorComputationHelper sch);

	@Override
	public final int size() {
		return mAlreadyConstrucedAutomaton.size();
	}

	@Override
	public final Set<CodeBlock> getAlphabet() {
		return mAlreadyConstrucedAutomaton.getAlphabet();
	}

	@Override
	public final String sizeInformation() {
		if (mInputInterpolantAutomaton == null) {
			return "yet neither states nor transitions";
		}
		return mInputInterpolantAutomaton.sizeInformation();
	}

	@Override
	public final Set<CodeBlock> getInternalAlphabet() {
		return mAlreadyConstrucedAutomaton.getInternalAlphabet();
	}

	@Override
	public final Set<CodeBlock> getCallAlphabet() {
		return mAlreadyConstrucedAutomaton.getCallAlphabet();
	}

	@Override
	public final Set<CodeBlock> getReturnAlphabet() {
		return mAlreadyConstrucedAutomaton.getReturnAlphabet();
	}

	@Override
	public final IStateFactory<IPredicate> getStateFactory() {
		return mAlreadyConstrucedAutomaton.getStateFactory();
	}

	@Override
	public final IPredicate getEmptyStackState() {
		return mAlreadyConstrucedAutomaton.getEmptyStackState();
	}

	@Override
	public final Iterable<IPredicate> getInitialStates() {
		return mAlreadyConstrucedAutomaton.getInitialStates();
	}

	@Override
	public final boolean isInitial(final IPredicate state) {
		return mAlreadyConstrucedAutomaton.isInitial(state);
	}

	@Override
	public final boolean isFinal(final IPredicate state) {
		return mAlreadyConstrucedAutomaton.isFinal(state);
	}

	@Override
	public final Set<CodeBlock> lettersInternal(final IPredicate state) {
		return getInternalAlphabet();
	}

	@Override
	public final Set<CodeBlock> lettersCall(final IPredicate state) {
		return getCallAlphabet();
	}

	@Override
	public final Set<CodeBlock> lettersReturn(final IPredicate state) {
		return getReturnAlphabet();
	}

	@Override
	public final Iterable<OutgoingInternalTransition<CodeBlock, IPredicate>> internalSuccessors(final IPredicate state,
			final CodeBlock letter) {
		if (mMode == Mode.ON_DEMAND_CONSTRUCTION) {
			if (!mSuccessorComputationBookkeeping.areInternalSuccsComputed(state, letter)) {
				computeSuccs(state, null, letter, mInSucComp);
			}
		}
		return mAlreadyConstrucedAutomaton.internalSuccessors(state, letter);
	}

	@Override
	public final Iterable<OutgoingInternalTransition<CodeBlock, IPredicate>>
			internalSuccessors(final IPredicate state) {
		if (mMode == Mode.ON_DEMAND_CONSTRUCTION) {
			for (final CodeBlock letter : lettersInternal(state)) {
				if (!mSuccessorComputationBookkeeping.areInternalSuccsComputed(state, letter)) {
					computeSuccs(state, null, letter, mInSucComp);
				}
			}
		}
		return mAlreadyConstrucedAutomaton.internalSuccessors(state);
	}

	@Override
	public final Iterable<OutgoingCallTransition<CodeBlock, IPredicate>> callSuccessors(final IPredicate state,
			final CodeBlock letter) {
		final Call call = (Call) letter;
		if (mMode == Mode.ON_DEMAND_CONSTRUCTION) {
			if (!mSuccessorComputationBookkeeping.areCallSuccsComputed(state, call)) {
				computeSuccs(state, null, letter, mCaSucComp);
			}
		}
		return mAlreadyConstrucedAutomaton.callSuccessors(state, call);
	}

	@Override
	public final Iterable<OutgoingCallTransition<CodeBlock, IPredicate>> callSuccessors(final IPredicate state) {
		if (mMode == Mode.ON_DEMAND_CONSTRUCTION) {
			for (final CodeBlock letter : lettersCall(state)) {
				final Call call = (Call) letter;
				if (!mAlreadyConstrucedAutomaton.callSuccessors(state, call).iterator().hasNext()) {
					computeSuccs(state, null, letter, mCaSucComp);
				}
			}
		}
		return mAlreadyConstrucedAutomaton.callSuccessors(state);
	}

	@Override
	public final Iterable<OutgoingReturnTransition<CodeBlock, IPredicate>> returnSuccessors(final IPredicate state,
			final IPredicate hier, final CodeBlock letter) {
		final Return ret = (Return) letter;
		if (mMode == Mode.ON_DEMAND_CONSTRUCTION) {
			if (!mSuccessorComputationBookkeeping.areReturnSuccsComputed(state, hier, ret)) {
				computeSuccs(state, hier, letter, mReSucComp);
			}
		}
		return mAlreadyConstrucedAutomaton.returnSuccessors(state, hier, ret);
	}

	@Override
	public final Iterable<OutgoingReturnTransition<CodeBlock, IPredicate>>
			returnSuccessorsGivenHier(final IPredicate state, final IPredicate hier) {
		if (mMode == Mode.ON_DEMAND_CONSTRUCTION) {
			for (final CodeBlock letter : lettersReturn(state)) {
				final Return ret = (Return) letter;
				if (!mAlreadyConstrucedAutomaton.returnSuccessors(state, hier, ret).iterator().hasNext()) {
					computeSuccs(state, hier, letter, mReSucComp);
				}
			}
		}
		return mAlreadyConstrucedAutomaton.returnSuccessorsGivenHier(state, hier);
	}

	@Override
	public final String toString() {
		if (mMode == Mode.READ_ONLY) {
			return (new AutomatonDefinitionPrinter<String, String>(new AutomataLibraryServices(mServices), "nwa",
					Format.ATS, this)).getDefinitionAsString();
		}
		return "automaton under construction";
	}

	/**
	 * Abstract class for successor computation. Subclasses are the successor computations for internal, call, and
	 * return. Because we can only override methods with the same signature (in Java) we use the 3-parameter-signature
	 * for return (with hierarchical state) and use null as hierarchical state for call and internal.
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
		public boolean isLinearPredecessorFalse(final IPredicate resPred) {
			return resPred == mIaFalseState;
		}

		@Override
		public boolean isHierarchicalPredecessorFalse(final IPredicate resHier) {
			assert resHier == null;
			return false;
		}

		@Override
		public void addTransition(final IPredicate resPred, final IPredicate resHier, final CodeBlock letter,
				final IPredicate inputSucc) {
			assert resHier == null;
			mAlreadyConstrucedAutomaton.addInternalTransition(resPred, letter, inputSucc);
		}

		@Override
		public Validity computeSuccWithSolver(final IPredicate resPred, final IPredicate resHier,
				final CodeBlock letter, final IPredicate inputSucc) {
			assert resHier == null;
			return mIHoareTripleChecker.checkInternal(resPred, (IInternalAction) letter, inputSucc);
		}

		@Override
		public Collection<IPredicate> getSuccsInterpolantAutomaton(final IPredicate resPred, final IPredicate resHier,
				final CodeBlock letter) {
			assert resHier == null;
			final Collection<IPredicate> succs = NestedWordAutomataUtils.constructInternalSuccessors(
					mInputInterpolantAutomaton, resPred, letter);
			if (succs == null) {
				return Collections.emptySet();
			}
			return succs;
		}

		@Override
		public void reportSuccsComputed(final IPredicate resPred, final IPredicate resHier, final CodeBlock letter) {
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
		public void addTransition(final IPredicate resPred, final IPredicate resHier, final CodeBlock letter,
				final IPredicate inputSucc) {
			assert resHier == null;
			mAlreadyConstrucedAutomaton.addCallTransition(resPred, letter, inputSucc);
		}

		@Override
		public Validity computeSuccWithSolver(final IPredicate resPred, final IPredicate resHier,
				final CodeBlock letter, final IPredicate inputSucc) {
			assert resHier == null;
			return mIHoareTripleChecker.checkCall(resPred, (ICallAction) letter, inputSucc);
		}

		@Override
		public Collection<IPredicate> getSuccsInterpolantAutomaton(final IPredicate resPred, final IPredicate resHier,
				final CodeBlock letter) {
			assert resHier == null;
			final Collection<IPredicate> succs = NestedWordAutomataUtils.constructCallSuccessors(
						mInputInterpolantAutomaton, resPred, letter);
			if (succs == null) {
				return Collections.emptySet();
			}
			return succs;
		}

		@Override
		public void reportSuccsComputed(final IPredicate resPred, final IPredicate resHier, final CodeBlock letter) {
			assert resHier == null;
			mSuccessorComputationBookkeeping.reportCallSuccsComputed(resPred, (Call) letter);
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
		public void addTransition(final IPredicate resPred, final IPredicate resHier, final CodeBlock letter,
				final IPredicate inputSucc) {
			mAlreadyConstrucedAutomaton.addReturnTransition(resPred, resHier, letter, inputSucc);
		}

		@Override
		public Validity computeSuccWithSolver(final IPredicate resPred, final IPredicate resHier,
				final CodeBlock letter, final IPredicate inputSucc) {
			return mIHoareTripleChecker.checkReturn(resPred, resHier, (IReturnAction) letter, inputSucc);
		}

		@Override
		public Collection<IPredicate> getSuccsInterpolantAutomaton(final IPredicate resPred, final IPredicate resHier,
				final CodeBlock letter) {
			final Collection<IPredicate> succs = NestedWordAutomataUtils.constructReturnSuccessors(
					mInputInterpolantAutomaton, resPred, resHier, letter);
			if (succs == null) {
				return Collections.emptySet();
			}
			return succs;
		}

		@Override
		public void reportSuccsComputed(final IPredicate resPred, final IPredicate resHier, final CodeBlock letter) {
			mSuccessorComputationBookkeeping.reportReturnSuccsComputed(resPred, resHier, (Return) letter);
		}

	}

	/**
	 * Objects that implement this interface provide information if successors have already been computed.
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
		abstract void reportReturnSuccsComputed(IPredicate state, IPredicate hier, Return ret);
	}

	/**
	 * Default implementation of {@link ISuccessorComputationBookkeeping} uses a NwaCacheBookkeeping to store which
	 * successors have already been computed.
	 */
	private class DefaultSuccessorComputationBookkeeping implements ISuccessorComputationBookkeeping {

		private final NwaCacheBookkeeping<CodeBlock, IPredicate> mResultBookkeeping = new NwaCacheBookkeeping<>();

		@Override
		public boolean areInternalSuccsComputed(final IPredicate state, final CodeBlock letter) {
			return mResultBookkeeping.isCachedInternal(state, letter);
		}

		@Override
		public void reportInternalSuccsComputed(final IPredicate state, final CodeBlock letter) {
			mResultBookkeeping.reportCachedInternal(state, letter);
		}

		@Override
		public boolean areCallSuccsComputed(final IPredicate state, final Call call) {
			return mResultBookkeeping.isCachedCall(state, call);
		}

		@Override
		public void reportCallSuccsComputed(final IPredicate state, final Call call) {
			mResultBookkeeping.reportCachedCall(state, call);
		}

		@Override
		public boolean areReturnSuccsComputed(final IPredicate state, final IPredicate hier, final Return ret) {
			return mResultBookkeeping.isCachedReturn(state, hier, ret);
		}

		@Override
		public void reportReturnSuccsComputed(final IPredicate state, final IPredicate hier, final Return ret) {
			mResultBookkeeping.reportCachedReturn(state, hier, ret);
		}

	}

	/**
	 * Implementation of {@link ISuccessorComputationBookkeeping} that avoids an additional bookkeeping but works only
	 * if we construct a total automata. Idea: If there is no successor, we have not yet computed the successors,
	 * because there would be at least one since the automaton is total. (An automaton is total if for each state and
	 * each letter, there is at least one outgoing transition)
	 */
	private class SuccessorComputationBookkeepingForTotalAutomata implements ISuccessorComputationBookkeeping {

		@Override
		public boolean areInternalSuccsComputed(final IPredicate state, final CodeBlock letter) {
			final Collection<IPredicate> succs = mAlreadyConstrucedAutomaton.succInternal(state, letter);
			if (succs == null) {
				return false;
			}
			return succs.iterator().hasNext();
		}

		@Override
		public boolean areCallSuccsComputed(final IPredicate state, final Call call) {
			final Collection<IPredicate> succs = mAlreadyConstrucedAutomaton.succCall(state, call);
			if (succs == null) {
				return false;
			}
			return succs.iterator().hasNext();
		}

		@Override
		public boolean areReturnSuccsComputed(final IPredicate state, final IPredicate hier, final Return ret) {
			final Collection<IPredicate> succs = mAlreadyConstrucedAutomaton.succReturn(state, hier, ret);
			if (succs == null) {
				return false;
			}
			return succs.iterator().hasNext();
		}

		@Override
		public void reportInternalSuccsComputed(final IPredicate state, final CodeBlock letter) {
			// do nothing, information is implicitly stored in total automaton
		}

		@Override
		public void reportCallSuccsComputed(final IPredicate state, final Call call) {
			// do nothing, information is implicitly stored in total automaton
		}

		@Override
		public void reportReturnSuccsComputed(final IPredicate state, final IPredicate hier, final Return ret) {
			// do nothing, information is implicitly stored in total automaton
		}

	}

}
