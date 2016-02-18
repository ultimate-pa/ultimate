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

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiClosureNwa;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.model.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IAnalysis;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core.ATester;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core.AutomatonDeltaDebuggerObserver;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatondeltadebugger.shrinkers.AShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatondeltadebugger.shrinkers.CallTransitionShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatondeltadebugger.shrinkers.InternalTransitionShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatondeltadebugger.shrinkers.NormalizeStateShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatondeltadebugger.shrinkers.ReturnTransitionShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatondeltadebugger.shrinkers.SingleExitShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatondeltadebugger.shrinkers.StateShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatondeltadebugger.shrinkers.UnusedLetterShrinker;

/**
 * Ultimate interface to the automaton delta debugger.
 * 
 * NOTE: A user must change the code at three places: - the tester (which
 * specifies which operation is run) - the list of rules to be applied
 * iteratively - the list of rules to be applied only once in the end The class
 * provides some default values here.
 * 
 * @see getTester
 * @see getShrinkersLoop
 * @see getShrinkersEnd
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
	public GraphType getOutputDefinition() {
		return null;
	}
	
	@Override
	public boolean isGuiRequired() {
		return false;
	}
	
	@Override
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.LAST;
	}
	
	@Override
	public List<String> getDesiredToolID() {
		return null;
	}
	
	@Override
	public void setInputDefinition(GraphType graphType) {
		mLogger.info("Receiving input definition " + graphType.toString());
		mObservers.clear();
		
		String creator = graphType.getCreator();
		switch (creator) {
			case "de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser":
				mLogger.info("Preparing to process Automata...");
				mObservers
						.add(new AutomatonDeltaDebuggerObserver<LETTER, STATE>(
								mServices, getTester(), getShrinkersLoop(),
								getShrinkersEnd()));
				break;
			default:
				mLogger.warn("Ignoring input definition " + creator);
		}
	}
	
	/**
	 * NOTE: Insert an instance of a throwable and one of the automaton library
	 * methods here.
	 * 
	 * @return tester which listens for the specified throwable
	 */
	private ATester<LETTER, STATE> getTester() {
		// example, use your own throwable here
		final Throwable throwable = new Exception();
		
		// example, use your own method here
		return new ATester<LETTER, STATE>(throwable) {
			@Override
			public void execute(INestedWordAutomaton<LETTER, STATE> automaton)
					throws Throwable {
				new BuchiClosureNwa<LETTER, STATE>(new AutomataLibraryServices(mServices), automaton);
			}
		};
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
	public UltimatePreferenceInitializer getPreferences() {
		return null;
	}
	
	@Override
	public void setToolchainStorage(IToolchainStorage services) {
	
	}
	
	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}
	
	@Override
	public void finish() {
	
	}
}
