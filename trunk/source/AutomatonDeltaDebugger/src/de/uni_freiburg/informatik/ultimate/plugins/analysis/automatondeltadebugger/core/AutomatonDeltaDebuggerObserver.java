/*
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core.AbstractDebug.DebugPolicy;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.factories.INestedWordAutomatonFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.factories.NestedWordAutomatonFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.AbstractShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.BridgeShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.AutomataDefinitionInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataDefinitionsAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;

/**
 * Obeserver which initializes the delta debugging process.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 * @see AutomatonDebugger
 */
public class AutomatonDeltaDebuggerObserver<LETTER, STATE> extends BaseObserver {
	private final IUltimateServiceProvider mServices;
	private final AbstractTester<LETTER, STATE> mTester;
	private final List<AbstractShrinker<?, LETTER, STATE>> mShrinkersLoop;
	private final List<BridgeShrinker<?, LETTER, STATE>> mShrinkersBridge;
	private final List<AbstractShrinker<?, LETTER, STATE>> mShrinkersEnd;
	private final DebugPolicy mPolicy;
	private final ILogger mLogger;

	/**
	 * @param services
	 *            Ultimate services.
	 * @param tester
	 *            tester
	 * @param shrinkersLoop
	 *            rules to be appplied iteratively
	 * @param shrinkersBridge
	 *            rules to be applied after each loop with changes
	 * @param shrinkersEnd
	 *            rules to be applied once in the end
	 * @param policy
	 *            debug policy
	 */
	public AutomatonDeltaDebuggerObserver(final IUltimateServiceProvider services,
			final AbstractTester<LETTER, STATE> tester, final List<AbstractShrinker<?, LETTER, STATE>> shrinkersLoop,
			final List<BridgeShrinker<?, LETTER, STATE>> shrinkersBridge,
			final List<AbstractShrinker<?, LETTER, STATE>> shrinkersEnd, final DebugPolicy policy) {
		mServices = services;
		mTester = tester;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mShrinkersLoop = new ArrayList<>(shrinkersLoop);
		mShrinkersBridge = new ArrayList<>(shrinkersBridge);
		mShrinkersEnd = new ArrayList<>(shrinkersEnd);
		mPolicy = policy;
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean process(final IElement root) throws Throwable {
		if (!(root instanceof AutomataTestFileAST)) {
			return true;
		}
		final AutomataDefinitionsAST automataDefinition = ((AutomataTestFileAST) root).getAutomataDefinitions();
		final AutomataDefinitionInterpreter adi = new AutomataDefinitionInterpreter(null, mLogger, mServices);
		adi.interpret(automataDefinition);
		final Map<String, Object> automata = adi.getAutomata();
		// design decision: take the first automaton from the iterator
		INestedWordAutomaton<LETTER, STATE> automaton = null;
		for (final Object object : automata.values()) {
			if (object instanceof INestedWordAutomaton<?, ?>) {
				automaton = (INestedWordAutomaton<LETTER, STATE>) object;
				break;
			}
		}
		if (automaton == null) {
			mLogger.info("The input file did not contain any nested word automaton (type INestedWordAutomaton).");
			return true;
		}
		deltaDebug(automaton);
		return false;
	}

	/**
	 * initializes and runs the delta debugging process
	 * <p>
	 * NOTE: A user may want to change the type of automaton factory here.
	 * 
	 * @param automaton
	 *            input automaton
	 */
	private void deltaDebug(final INestedWordAutomaton<LETTER, STATE> automaton) {
		// automaton factory
		final INestedWordAutomatonFactory<LETTER, STATE> automatonFactory =
				new NestedWordAutomatonFactory<>(mServices, automaton);

		// construct delta debugger
		final AutomatonDebugger<LETTER, STATE> debugger =
				new AutomatonDebugger<>(mServices, automaton, automatonFactory, mTester);

		// execute delta debugger (binary search)
		final INestedWordAutomaton<LETTER, STATE> result =
				debugger.shrink(mShrinkersLoop, mShrinkersBridge, mShrinkersEnd, mPolicy);

		// print result
		mLogger.info("The automaton debugger terminated, resulting in the following automaton:");
		mLogger.info(result);
	}
}
