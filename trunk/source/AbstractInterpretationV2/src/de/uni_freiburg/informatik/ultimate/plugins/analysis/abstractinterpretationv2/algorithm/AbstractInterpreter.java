package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState.ComparisonResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class AbstractInterpreter<ACTION, VARDECL> {

	// TODO: Replace with setting by replacing all reads with accesses to
	// ultimatepreferencestorage, i.e. final UltimatePreferenceStore preferences
	// = new UltimatePreferenceStore(Activator.PLUGIN_ID);
	private static final int MAX_UNWINDINGS = 10;

	private final ITransitionProvider<ACTION> mTransitionProvider;
	private final IUltimateServiceProvider mServices;
	private final Logger mLogger;
	private final IAbstractStateStorage<ACTION, VARDECL> mStateStorage;
	private final IAbstractDomain<ACTION, VARDECL> mDomain;
	private final IVariableProvider<ACTION, VARDECL> mVarProvider;
	private final ILoopDetector<ACTION> mLoopDetector;

	public AbstractInterpreter(IUltimateServiceProvider services, ITransitionProvider<ACTION> post,
			IAbstractStateStorage<ACTION, VARDECL> storage, IAbstractDomain<ACTION, VARDECL> domain,
			IVariableProvider<ACTION, VARDECL> varProvider, ILoopDetector<ACTION> loopDetector) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mTransitionProvider = post;
		mStateStorage = storage;
		mDomain = domain;
		mVarProvider = varProvider;
		mLoopDetector = loopDetector;
	}

	public void process(ACTION elem) {
		final Deque<ACTION> worklist = new ArrayDeque<ACTION>();
		final Stack<Pair<ACTION,ACTION>> activeLoops = new Stack<>();
		final Map<Pair<ACTION,ACTION>,Integer> loopCounters = new HashMap<>();
		final IAbstractPostOperator<ACTION, VARDECL> post = mDomain.getPostOperator();
		final IAbstractStateBinaryOperator<ACTION, VARDECL> widening = mDomain.getWideningOperator();

		worklist.add(elem);
		
		while (!worklist.isEmpty()) {
			final ACTION current = worklist.removeFirst();
			IAbstractState<ACTION, VARDECL> preState = mStateStorage.getCurrentAbstractPreState(current);
			if (preState == null) {
				preState = mDomain.createFreshState();
				preState = mVarProvider.defineVariablesPre(current, preState);
				mStateStorage.addAbstractPreState(current, preState);
			}

			final IAbstractState<ACTION, VARDECL> oldPostState = mStateStorage.getCurrentAbstractPostState(current);

			if (oldPostState != null) {
				if (oldPostState.isBottom()) {
					// unreachable, just continue (do not add successors to
					// worklist)
					continue;
				}
				if (oldPostState.isFixpoint()) {
					// already fixpoint, just continue (do not add successors to
					// worklist)
					continue;
				}
			}

			final IAbstractState<ACTION, VARDECL> newPostState = post.apply(preState, current);
			final ComparisonResult comparisonResult = newPostState.compareTo(oldPostState);

			if (comparisonResult == ComparisonResult.EQUAL) {
				// found fixpoint, do not add new post state, mark old post
				// state as fixpoint, do not add successors to worklist
				mStateStorage.setPostStateIsFixpoint(current, oldPostState, true);
				continue;
			}

			if(!activeLoops.isEmpty()){
				//are we leaving a loop?
				Pair<ACTION, ACTION> lastPair = activeLoops.peek();
				if(lastPair.getSecond().equals(current)){
					//yes, we are leaving a loop
					activeLoops.pop();
//					loopCounters.
				}
			}
			
			ACTION loopExit = mLoopDetector.getLoopExit(current);
			if(loopExit != null){
				// we are entering a loop
				
			}
			
			Collection<IAbstractState<ACTION, VARDECL>> oldPostStates = mStateStorage.getAbstractPostStates(current);
			if (oldPostStates.size() > MAX_UNWINDINGS) {
				// we have more states than allowed unwindings at this location,
				// apply widening
			}

			if (newPostState.isBottom()) {

			}

			// TODO: LoopDetector, ScopeDetector (?), saving new abstract state,
			// applying merge, applying widening, preferences
		}
	}
}
