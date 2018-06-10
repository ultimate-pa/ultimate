/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automaton Delta Debugger.
 * 
 * The ULTIMATE Automaton Delta Debugger is free software: you can redistribute
 * it and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * The ULTIMATE Automaton Delta Debugger is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser
 * General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automaton Delta Debugger. If not, see
 * <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automaton Delta Debugger, or any covered work, by linking or
 * combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automaton Delta Debugger grant you additional
 * permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.IAnalysis;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.AutomatonDebuggerExamples.EOperationType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.AutomatonDebuggerTesters.EAutomatonDeltaDebuggerTestMode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core.AbstractDebug.DebugPolicy;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core.AbstractTester;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core.AutomatonDeltaDebuggerObserver;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.AbstractShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.BridgeShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.CallReturnChainShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.CallTransitionShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.ChangeInitialStatesShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.CommonSingleExitShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.InternalTransitionShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.NormalizeStateShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.ReturnTransitionShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.SingleExitShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.StateShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.UnusedLetterShrinker;

/**
 * Ultimate interface to the automaton delta debugger.
 * <p>
 * NOTE: A user may change the code at the following places:
 * <ol>
 * <li>the tester (which specifies which operation is run, mandatory change)</li>
 * <li>the list of rules to be applied iteratively (optional change) {@link #getShrinkersLoop()}</li>
 * <li>the list of rules to be applied after each loop with changes (optional change) {@link #getShrinkersBridge()}</li>
 * <li>the list of rules to be applied only once in the end (optional change) {@link #getShrinkersEnd()}</li>
 * <li>the policy according to which list items are executed (optional change)</li>
 * </ol>
 * The class provides some default values here.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class AutomatonDeltaDebugger implements IAnalysis {
	protected ILogger mLogger;
	protected final List<IObserver> mObservers;
	private IUltimateServiceProvider mServices;

	// debug mode
	private final EAutomatonDeltaDebuggerTestMode mOperationMode;
	// debugged operation
	private final EOperationType mOperationType;
	// internal debug policy
	private final DebugPolicy mDebugPolicy;

	/**
	 * Standard automaton delta debugger.
	 */
	public AutomatonDeltaDebugger() {
		mObservers = new LinkedList<>();
		/*
		 * NOTE: Insert your own settings here.
		 */
		mOperationMode = EAutomatonDeltaDebuggerTestMode.GENERAL;
		mOperationType = EOperationType.EXCEPTION_DUMMY;
		mDebugPolicy = DebugPolicy.BINARY;
	}

	@Override
	public void setInputDefinition(final ModelType graphType) {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Receiving input definition " + graphType);
		}
		mObservers.clear();

		final String creator = graphType.getCreator();
		if ("de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser".equals(creator)) {
			if (mLogger.isInfoEnabled()) {
				mLogger.info("Preparing to process automaton...");
			}
			final AbstractTester<String, String> tester =
					new AutomatonDebuggerTesters(mServices).getTester(mOperationMode, mOperationType);
			mObservers.add(new AutomatonDeltaDebuggerObserver<>(mServices, tester, getShrinkersLoop(),
					getShrinkersBridge(), getShrinkersEnd(), mDebugPolicy));
		} else {
			if (mLogger.isWarnEnabled()) {
				mLogger.warn("Ignoring input definition " + creator);
			}
		}
	}

	/**
	 * NOTE: Insert or remove shrinkers here.
	 * 
	 * @return list of shrinkers (i.e., rules to apply) to be applied iteratively
	 */
	private List<AbstractShrinker<?, String, String>> getShrinkersLoop() {
		final List<AbstractShrinker<?, String, String>> shrinkersLoop = new ArrayList<>();

		// examples, use your own shrinkers here
		shrinkersLoop.add(new StateShrinker<>(mServices));
		shrinkersLoop.add(new InternalTransitionShrinker<>(mServices));
		shrinkersLoop.add(new CallTransitionShrinker<>(mServices));
		shrinkersLoop.add(new ReturnTransitionShrinker<>(mServices));
		shrinkersLoop.add(new SingleExitShrinker<>(mServices));
		shrinkersLoop.add(new CommonSingleExitShrinker<>(mServices));
		shrinkersLoop.add(new CallReturnChainShrinker<>(mServices));

		return shrinkersLoop;
	}

	/**
	 * NOTE: Insert or remove shrinkers here.
	 * 
	 * @return list of shrinkers (i.e., rules to apply) to be applied iteratively
	 */
	private List<BridgeShrinker<?, String, String>> getShrinkersBridge() {
		final List<BridgeShrinker<?, String, String>> shrinkersBridge = new ArrayList<>();

		// examples, use your own shrinkers here
		shrinkersBridge.add(new ChangeInitialStatesShrinker<>(mServices));

		return shrinkersBridge;
	}

	/**
	 * NOTE: Insert or remove shrinkers here.
	 * 
	 * @return list of shrinkers (i.e., rules to apply) to be applied only once
	 */
	private List<AbstractShrinker<?, String, String>> getShrinkersEnd() {
		final List<AbstractShrinker<?, String, String>> shrinkersEnd = new ArrayList<>();

		// examples, use your own shrinkers here
		shrinkersEnd.add(new UnusedLetterShrinker<>(mServices));
		shrinkersEnd.add(new NormalizeStateShrinker<>(mServices));

		return shrinkersEnd;
	}

	@Override
	public ModelType getOutputDefinition() {
		return null;
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public ModelQuery getModelQuery() {
		return ModelQuery.LAST;
	}

	@Override
	public List<String> getDesiredToolIds() {
		return Collections.emptyList();
	}

	@Override
	public List<IObserver> getObservers() {
		return mObservers;
	}

	@Override
	public void init() {
		//no init needed
	}

	@Override
	public String getPluginName() {
		return Activator.PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return null;
	}

	@Override
	public void setToolchainStorage(final IToolchainStorage services) {
		//no storage needed
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void finish() {
		//no finish needed
	}
}
