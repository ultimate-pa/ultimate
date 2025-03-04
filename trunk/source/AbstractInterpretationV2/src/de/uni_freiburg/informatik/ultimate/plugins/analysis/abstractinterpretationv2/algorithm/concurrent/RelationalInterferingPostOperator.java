package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadCurrent;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadOther;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;

public class RelationalInterferingPostOperator<STATE extends IAbstractState<STATE>, ACTION extends IcfgEdge>
		implements IAbstractPostOperator<RelationalInterferingState<STATE, ACTION>, ACTION> {
	private String mCurrentThreadName;
	private final IDomain mSifaDomain;
	private final IUltimateServiceProvider mServiceProvider;

	private final ILogger mLogger;

	private final AbstractInterferenceState<STATE, ACTION> mInterferences;
	private final CfgSmtToolkit mToolkit;
	private final IAbstractDomain<STATE, ACTION> mUnderlyingDomain;
	private final IAbstractPostOperator<STATE, ACTION> mUnderlyingPostOp;
	private final RelationalInterferingDomain<STATE, ACTION> mRelationalInterferingDomain;

	public RelationalInterferingPostOperator(final IDomain sifaDomain, final IIcfg<?> cfg,
			final IUltimateServiceProvider serviceProvider,
			final AbstractInterferenceState<STATE, ACTION> interferences,
			final IAbstractDomain<STATE, ACTION> underlying, final IAbstractPostOperator<STATE, ACTION> postOp,
			final RelationalInterferingDomain<STATE, ACTION> relationalInterferingDomain) {
		mLogger = serviceProvider.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSifaDomain = sifaDomain;
		mServiceProvider = serviceProvider;
		mInterferences = interferences;
		mToolkit = cfg.getCfgSmtToolkit();
		mUnderlyingDomain = underlying;
		mUnderlyingPostOp = postOp;
		mRelationalInterferingDomain = relationalInterferingDomain;
	}

	@Override
	public Collection<RelationalInterferingState<STATE, ACTION>>
			apply(final RelationalInterferingState<STATE, ACTION> oldstate, final ACTION transition) {
		if (oldstate.isBottom()) {
			return List.of(oldstate);
		}
		mLogger.error("START postOperator----------------");
		mLogger.error("current Thread: " + transition.getPrecedingProcedure());
		mCurrentThreadName = transition.getPrecedingProcedure();

		if (transition instanceof ForkThreadCurrent || transition instanceof ForkThreadOther) {
			mLogger.warn("Fork transition, no postOp, no interference created");
			return applyFork(oldstate, transition);
		}
		mLogger.warn("Applying postoperator to ");
		mLogger.warn("state: " + oldstate.toLogString());
		mLogger.warn("transitionTerm: " + transition);
		mLogger.info("locals: " + mToolkit.getSymbolTable().getLocals(mCurrentThreadName));

		// 1. normal poststate
		var postRelationalState = new RelationalInterferingState<>(mUnderlyingDomain,
				mUnderlyingPostOp.apply(oldstate.getSTATE(), transition), oldstate.getThreadInstanceState(),
				mInterferences);
		mLogger.warn("state after: " + postRelationalState);

		// TODO: alpha it ?
		// alpha(state) (TODO: atm doesnt alpha thread/loc info)

		// 2. Add new interference to global map
		if (isInterferingTransition(transition)) {
			mInterferences.addInterference(mCurrentThreadName, transition, oldstate.getSTATE());
			mLogger.error("Interference created: " + oldstate.getSTATE().toLogString() + " "
					+ transition.getTransformula().toStringDirect());
		}

		// 3. apply interferences
		// TODO: check if topstate
		postRelationalState = stateAfterInterferences(postRelationalState, mCurrentThreadName);
		mLogger.warn("state after interferences: " + postRelationalState);

		mLogger.error("----------------END postOperator");
		return List.of(postRelationalState);
	}

	private boolean isInterferingTransition(final ACTION transition) {
		if (!(transition instanceof final StatementSequence statementSequence)) {
			return true;
		}
		for (final Statement statement : statementSequence.getStatements()) {
			if (!(statement instanceof AssumeStatement)) {
				return true;
			}
		}
		return false;
	}

	private Collection<RelationalInterferingState<STATE, ACTION>>
			applyFork(final RelationalInterferingState<STATE, ACTION> oldstate, final ACTION transition) {
		var newState = oldstate;
		// increment threadcounter of forked thread and all threads who are forked, etc,
		// by forked
		if (transition instanceof final ForkThreadCurrent fork1) {
			final var forked = fork1.getNameOfForkedProcedure();
			if (!mInterferences.getSeenForks().contains(fork1)) {
				mInterferences.update(transition.getPrecedingProcedure(), forked);
				mInterferences.getSeenForks().add(fork1);
			}
			for (final String thread : mInterferences.getActiveIfActive().getImage(forked)) {
				newState.getThreadInstanceState().setActive(thread);
			}
		} else if (transition instanceof ForkThreadOther) {
			throw new IllegalArgumentException("Unsupported fork transition type");
		}
		// apply interferences
		newState = stateAfterInterferences(newState, mCurrentThreadName);
		return List.of(newState);
	}

	public RelationalInterferingState<STATE, ACTION> stateAfterInterferences(
			final RelationalInterferingState<STATE, ACTION> oldstate, final String ownerThread) {
		final Set<String> threadNameSet = oldstate.getThreadInstanceState().getThreadNameSet();
		final Set<String> possibleInterferenceSet = new HashSet<>();
		final var procedureMap = oldstate.getThreadInstanceState().getThreadInstances();
		for (final String threadName : threadNameSet) {
			final int threadInstances = procedureMap.get(threadName);
			if (threadInstances >= 2 || threadName != ownerThread && threadInstances > 0) {
				possibleInterferenceSet.add(threadName);
			}
		}

		return oldstate.union(interferenceFixpoint(possibleInterferenceSet, oldstate));
	}

	private RelationalInterferingState<STATE, ACTION> interferenceFixpoint(final Set<String> interferenceSet,
			final RelationalInterferingState<STATE, ACTION> state) {
		int iterations = 0;
		var newState = state;
		boolean changed = true;
		while (changed) {
			iterations++;
			final var beginLoopState = new RelationalInterferingState<>(mUnderlyingDomain, newState.getSTATE(),
					newState.getThreadInstanceState(), mInterferences);
			for (final String interference : interferenceSet) {
				final var interferenceMap = mInterferences.getInterferenceMapHashRelation().get(interference);
				if (mInterferences.getInterferencesForThread(interference) == null) {
					continue;
				}
				for (final ACTION interferenceAction : interferenceMap.keySet()) {
					if (newState.isBottom()) {
						mLogger.warn("aborting interferencefixpoint, state is bottom");
						return newState;
					}
					mLogger.warn("Applying interference: " + interferenceAction.getTransformula().getClosedFormula()
							+ " " + interferenceMap.get(interferenceAction));
					mLogger.warn("to state: " + newState.getSTATE().toLogString());
					final var postState = new RelationalInterferingState<>(mUnderlyingDomain,
							mUnderlyingPostOp.apply(newState.getSTATE(), interferenceAction),
							newState.getThreadInstanceState(), mInterferences);

					if (iterations < 3) {
						newState = newState.union(postState);
						mLogger.warn("result: " + newState);
					} else {
						newState = mRelationalInterferingDomain.getWideningOperator().apply(newState, postState);
						mLogger.warn("Widening result: " + newState);
					}
				}
			}
			changed = newState.isSubsetOf(beginLoopState) != SubsetResult.NONE ? false : true;
		}
		return newState;
	}

	@Override
	public List<RelationalInterferingState<STATE, ACTION>> apply(
			final RelationalInterferingState<STATE, ACTION> stateBeforeLeaving,
			final RelationalInterferingState<STATE, ACTION> secondState, final ACTION transition) {
		throw new UnsupportedOperationException("Not implemented.");
	}

	@Override
	public EvalResult evaluate(final RelationalInterferingState<STATE, ACTION> state, final Term formula,
			final Script script) {
		throw new UnsupportedOperationException("Not implemented.");
	}
}
