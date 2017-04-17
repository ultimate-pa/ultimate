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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core;

import java.util.Collections;
import java.util.List;
import java.util.ListIterator;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.AbstractShrinker;

/**
 * Reduces a list of objects in a binary search manner until a local minimum is found.
 * <p>
 * Note that the local minimum is only according to the current shrinker, i.e., the respective shrinker cannot be
 * applied to a subinterval of objects anymore while still producing the error. However, removing, say, objects 1 and 3
 * might still work.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <T>
 *            shrinker type
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class SingleDebug<T, LETTER, STATE> extends AbstractDebug<T, LETTER, STATE> {
	/**
	 * @param tester
	 *            Tester.
	 * @param shrinker
	 *            shrinker
	 */
	public SingleDebug(final AbstractTester<LETTER, STATE> tester, final AbstractShrinker<T, LETTER, STATE> shrinker) {
		super(tester, shrinker);
	}

	@Override
	public boolean run() {
		boolean result = false;
		final List<T> list = mShrinker.extractList();
		if (list.isEmpty()) {
			return result;
		}
		final ListIterator<T> iterator = list.listIterator();
		while (iterator.hasNext()) {
			if (mShrinker.isTimeoutRequested()) {
				return result;
			}

			// extract next element from the list
			final List<T> sublist = Collections.singletonList(iterator.next());

			// run test
			result |= super.test(sublist);

			if (mShrinker.isCancelRequested()) {
				break;
			}
		}
		return result;
	}

	@Override
	protected void errorAction() {
		// empty
	}

	@Override
	protected void noErrorAction() {
		// empty
	}
}
