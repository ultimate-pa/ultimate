/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core.AbstractDebug.DebugPolicy;

/**
 * A bridge shrinker has an internal state and hence can be interrupted while still continuing from the current state
 * later.
 * <p>
 * We use these shrinkers for normally non-converging changes such as swapping the initial state.<br>
 * Whenever the change still triggered the error, we try the main shrinkers again on the result. If this did not change
 * anything, we try the next bridge change (there are only finitely many of them).<br>
 * If any of the (successful) bridge changes triggered a further change by one of the main shrinkers, we follow this
 * change and discard any further possible bridge changes. The internal state of the bridge shrinker is then reset so
 * that it can be used again in a fresh run.<br>
 * If, on the other hand, no change by the bridge shrinker triggered a further change, the bridge shrinker is removed to
 * ensure termination eventually.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <T>
 *            type of objects to be changed, e.g., swapping initial states
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public abstract class BridgeShrinker<T, LETTER, STATE> extends AbstractShrinker<T, LETTER, STATE> {
	/**
	 * @param services
	 *            Ultimate services.
	 */
	public BridgeShrinker(final IUltimateServiceProvider services) {
		super(services);
	}

	/**
	 * Resets the internal state of the shrinker.
	 * 
	 * @param automaton
	 *            automaton to use henceforth
	 */
	public abstract void reset(INestedWordAutomaton<LETTER, STATE> automaton);

	/**
	 * @return true iff all possible changes have been applied.
	 */
	public abstract boolean isFinished();

	@Override
	public boolean isPolicyOverridden() {
		return true;
	}

	@Override
	public DebugPolicy getPolicy() {
		return DebugPolicy.SINGLE;
	}
}
