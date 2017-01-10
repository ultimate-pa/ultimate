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

import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.IAnalysis;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.AutomatonDebuggerExamples.EOperationType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core.AbstractDebug.DebugPolicy;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core.AbstractTester;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core.AutomatonDeltaDebuggerObserver;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core.DebuggerException;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.AbstractShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.BridgeShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.CallTransitionShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.ChangeInitialStatesShrinker;
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
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
@SuppressWarnings("squid:S1200")
public class AutomatonDeltaDebugger<LETTER, STATE> implements IAnalysis {
	protected ILogger mLogger;
	protected final List<IObserver> mObservers;
	private IUltimateServiceProvider mServices;
	
	// debug mode
	private final EAutomatonDeltaDebuggerOperationMode mOperationMode;
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
		mOperationMode = EAutomatonDeltaDebuggerOperationMode.GENERAL;
		mOperationType = EOperationType.MINIMIZE_NWA_MAXSAT2;
		mDebugPolicy = DebugPolicy.BINARY;
	}
	
	/**
	 * Possible mode of the debugger.
	 */
	public enum EAutomatonDeltaDebuggerOperationMode {
		/**
		 * The debugger watches for any kind of error. The result might be a different error from the one originally
		 * seen, but usually "any error is interesting".
		 */
		GENERAL,
		/**
		 * The debugger watches only for errors in the {@link IOperation#checkResult(IStateFactory)} method. All other
		 * errors are not considered important.
		 */
		CHECK_RESULT
	}
	
	@Override
	public void setInputDefinition(final ModelType graphType) {
		mLogger.info("Receiving input definition " + graphType.toString());
		mObservers.clear();
		
		final String creator = graphType.getCreator();
		if ("de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser".equals(creator)) {
			mLogger.info("Preparing to process automaton...");
			final AbstractTester<LETTER, STATE> tester;
			switch (mOperationMode) {
				case GENERAL:
					tester = getGeneralTester();
					break;
				
				case CHECK_RESULT:
					tester = getCheckResultTester();
					break;
				
				default:
					throw new IllegalArgumentException("Unknown mode.");
			}
			mObservers.add(new AutomatonDeltaDebuggerObserver<>(
					mServices, tester, getShrinkersLoop(), getShrinkersBridge(),
					getShrinkersEnd(), mDebugPolicy));
		} else {
			mLogger.warn("Ignoring input definition " + creator);
		}
	}
	
	/**
	 * Example tester for debugging general problems.
	 * 
	 * @return tester which listens for any throwable
	 */
	private AbstractTester<LETTER, STATE> getGeneralTester() {
		// 'null' stands for any exception
		final Throwable throwable = null;
		
		return new AbstractTester<LETTER, STATE>(throwable) {
			@Override
			public void execute(final INestedWordAutomaton<LETTER, STATE> automaton)
					throws Throwable {
				final IStateFactory<STATE> factory = automaton.getStateFactory();
				
				getIOperation(automaton, factory);
			}
		};
	}
	
	/**
	 * Example tester for debugging problems with the {@code checkResult()} method of {@code IOperation}.
	 * 
	 * @return tester which debugs the checkResult method
	 */
	private AbstractTester<LETTER, STATE> getCheckResultTester() {
		final String message = "'checkResult' failed";
		final Throwable throwable = new DebuggerException(message);
		
		return new AbstractTester<LETTER, STATE>(throwable) {
			@Override
			public void execute(final INestedWordAutomaton<LETTER, STATE> automaton)
					throws Throwable {
				final IStateFactory<STATE> factory = automaton.getStateFactory();
				
				final IOperation<LETTER, STATE> op = getIOperation(automaton, factory);
				
				// throws a fresh exception iff checkResult() fails
				if (!op.checkResult(factory)) {
					throw throwable;
				}
			}
		};
	}
	
	/**
	 * Constructs an {@link IOperation} object from the setting.
	 * 
	 * @param automaton
	 *            automaton
	 * @param factory
	 *            state factory
	 * @return IOperation instance
	 * @throws Throwable
	 *             when error occurs
	 */
	@SuppressWarnings("squid:S00112")
	private IOperation<LETTER, STATE> getIOperation(final INestedWordAutomaton<LETTER, STATE> automaton,
			final IStateFactory<STATE> factory) throws Throwable {
		final AutomatonDebuggerExamples<LETTER, STATE> examples = new AutomatonDebuggerExamples<>(mServices);
		
		return examples.getOperation(mOperationType, automaton, factory);
	}
	
	/**
	 * NOTE: Insert or remove shrinkers here.
	 * 
	 * @return list of shrinkers (i.e., rules to apply) to be applied iteratively
	 */
	private List<AbstractShrinker<?, LETTER, STATE>> getShrinkersLoop() {
		final List<AbstractShrinker<?, LETTER, STATE>> shrinkersLoop = new ArrayList<>();
		
		// examples, use your own shrinkers here
		shrinkersLoop.add(new StateShrinker<>(mServices));
		shrinkersLoop.add(new InternalTransitionShrinker<>(mServices));
		shrinkersLoop.add(new CallTransitionShrinker<>(mServices));
		shrinkersLoop.add(new ReturnTransitionShrinker<>(mServices));
		shrinkersLoop.add(new SingleExitShrinker<>(mServices));
		
		return shrinkersLoop;
	}
	
	/**
	 * NOTE: Insert or remove shrinkers here.
	 * 
	 * @return list of shrinkers (i.e., rules to apply) to be applied iteratively
	 */
	private List<BridgeShrinker<?, LETTER, STATE>> getShrinkersBridge() {
		final List<BridgeShrinker<?, LETTER, STATE>> shrinkersBridge = new ArrayList<>();
		
		// examples, use your own shrinkers here
		shrinkersBridge.add(new ChangeInitialStatesShrinker<>(mServices));
		
		return shrinkersBridge;
	}
	
	/**
	 * NOTE: Insert or remove shrinkers here.
	 * 
	 * @return list of shrinkers (i.e., rules to apply) to be applied only once
	 */
	private List<AbstractShrinker<?, LETTER, STATE>> getShrinkersEnd() {
		final List<AbstractShrinker<?, LETTER, STATE>> shrinkersEnd = new ArrayList<>();
		
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
