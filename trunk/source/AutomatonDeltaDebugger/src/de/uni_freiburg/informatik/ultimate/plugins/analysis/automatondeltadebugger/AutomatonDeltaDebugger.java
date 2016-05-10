/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
import java.util.LinkedList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiClosureNwa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.maxsat.MinimizeNwaMaxSAT;
import de.uni_freiburg.informatik.ultimate.core.model.IAnalysis;
import de.uni_freiburg.informatik.ultimate.core.model.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.model.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.models.ModelType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core.ATester;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core.AutomatonDeltaDebuggerObserver;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core.DebuggerException;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.AShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.CallTransitionShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.InternalTransitionShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.NormalizeStateShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.ReturnTransitionShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.SingleExitShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.StateShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.UnusedLetterShrinker;

/**
 * Ultimate interface to the automaton delta debugger.
 * 
 * NOTE: A user may change the code at three places: <br>
 * - the tester (which specifies which operation is run, mandatory change)
 * {@link #getGeneralTester()} or
 * {@link #getIOperation(INestedWordAutomaton, StateFactory)} <br>
 * - the list of rules to be applied iteratively (optional change)
 * {@link #getShrinkersLoop()} <br>
 * - the list of rules to be applied only once in the end (optional change)
 * {@link #getShrinkersEnd()} <br>
 * The class provides some default values here.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class AutomatonDeltaDebugger<LETTER, STATE> implements IAnalysis {
	protected Logger mLogger;
	protected final List<IObserver> mObservers;
	private IUltimateServiceProvider mServices;
	
	public AutomatonDeltaDebugger() {
		mObservers = new LinkedList<IObserver>();
	}
	
	@Override
	public void setInputDefinition(ModelType graphType) {
		mLogger.info("Receiving input definition " + graphType.toString());
		mObservers.clear();
		
		String creator = graphType.getCreator();
		switch (creator) {
			case "de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser":
				mLogger.info("Preparing to process Automata...");
				mObservers
						.add(new AutomatonDeltaDebuggerObserver<LETTER, STATE>(
								mServices, getCheckResultTester(),
								getShrinkersLoop(), getShrinkersEnd()));
				break;
			default:
				mLogger.warn("Ignoring input definition " + creator);
		}
	}
	
	/* --- change the following methods accordingly --- */
	
	/**
	 * example tester for debugging general problems
	 * 
	 * NOTE: Insert an instance of a throwable and one of the automaton library
	 * methods here.
	 * 
	 * @return tester which listens for the specified throwable
	 */
	@SuppressWarnings("unused")
	private ATester<LETTER, STATE> getGeneralTester() {
		// example, use your own throwable here
		final Throwable throwable = new Exception();
		
		// example, use your own method here
		return new ATester<LETTER, STATE>(throwable) {
			@Override
			public void execute(INestedWordAutomaton<LETTER, STATE> automaton)
					throws Throwable {
				new BuchiClosureNwa<LETTER, STATE>(
						new AutomataLibraryServices(mServices), automaton);
			}
		};
	}
	
	/**
	 * example tester for debugging problems with the <code>checkResult()</code>
	 * method of <code>IOperation</code>
	 * 
	 * @return tester which debugs the checkResult method
	 */
	private ATester<LETTER, STATE> getCheckResultTester() {
		// example, use your own thrower class here (not important)
		final Class<?> thrower = MinimizeNwaMaxSAT.class;
		
		final String message = "'checkResult' failed";
		final Throwable throwable = new DebuggerException(thrower, message);
		
		return new ATester<LETTER, STATE>(throwable) {
			@Override
			public void execute(INestedWordAutomaton<LETTER, STATE> automaton)
					throws Throwable {
				final StateFactory<STATE> factory = automaton.getStateFactory();
				
				// change the following method for a different IOperation
				final IOperation<LETTER, STATE> op =
						getIOperation(automaton, factory);
				
				// throws a fresh exception iff checkResult() fails
				if (!op.checkResult(factory)) {
					throw new DebuggerException(thrower, message);
				}
			}
		};
	}
	
	/**
	 * NOTE: Call your own method here.
	 * 
	 * @param automaton automaton
	 * @param factory state factory
	 * @return IOperation instance
	 * @throws Throwable when error occurs
	 */
	private IOperation<LETTER, STATE> getIOperation(
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final StateFactory<STATE> factory) throws Throwable {
		final AutomatonDebuggerExamples<LETTER, STATE> examples =
				new AutomatonDebuggerExamples<LETTER, STATE>(mServices);
		
		// example code, use your own method here
		return examples.ReduceNwaDirectSimulation(automaton, factory);
	}
	
	/**
	 * NOTE: Insert or remove shrinkers here.
	 * 
	 * @return list of shrinkers (i.e., rules to apply) to be applied
	 *         iteratively
	 */
	private List<AShrinker<?, LETTER, STATE>> getShrinkersLoop() {
		final List<AShrinker<?, LETTER, STATE>> shrinkersLoop =
				new ArrayList<AShrinker<?, LETTER, STATE>>();
		
		// examples, use your own shrinkers here
		shrinkersLoop.add(new StateShrinker<LETTER, STATE>());
		shrinkersLoop.add(new InternalTransitionShrinker<LETTER, STATE>());
		shrinkersLoop.add(new CallTransitionShrinker<LETTER, STATE>());
		shrinkersLoop.add(new ReturnTransitionShrinker<LETTER, STATE>());
		shrinkersLoop.add(new SingleExitShrinker<LETTER, STATE>());
		
		return shrinkersLoop;
	}
	
	/**
	 * NOTE: Insert or remove shrinkers here.
	 * 
	 * @return list of shrinkers (i.e., rules to apply) to be applied only once
	 */
	private List<AShrinker<?, LETTER, STATE>> getShrinkersEnd() {
		final List<AShrinker<?, LETTER, STATE>> shrinkersEnd =
				new ArrayList<AShrinker<?, LETTER, STATE>>();
		
		// examples, use your own shrinkers here
		shrinkersEnd.add(new UnusedLetterShrinker<LETTER, STATE>());
		shrinkersEnd.add(new NormalizeStateShrinker<LETTER, STATE>());
		
		return shrinkersEnd;
	}
	
	/* --- Ultimate related stuff --- */
	
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
	public List<String> getDesiredToolID() {
		return null;
	}
	
	@Override
	public List<IObserver> getObservers() {
		return mObservers;
	}
	
	@Override
	public void init() {
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
	public void setToolchainStorage(IToolchainStorage services) {
		;
	}
	
	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}
	
	@Override
	public void finish() {
		;
	}
}
