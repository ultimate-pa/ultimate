/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.incrementalinclusion;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * TODO: Documentation.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public abstract class AbstractIncrementalInclusionCheck<LETTER, STATE> {
	protected final AutomataLibraryServices mServices;
	protected final ILogger mLogger;

	private final INestedWordAutomatonSimple<LETTER, STATE> mNwaA;
	private final List<INestedWordAutomatonSimple<LETTER, STATE>> mNwaB = new ArrayList<>();

	/**
	 * Constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param nwaA
	 *            minuend
	 */
	public AbstractIncrementalInclusionCheck(final AutomataLibraryServices services,
			final INestedWordAutomatonSimple<LETTER, STATE> nwaA) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		if (nwaA == null) {
			throw new IllegalArgumentException("automaton A must not be null");
		}
		mNwaA = nwaA;
	}

	/**
	 * @return An accepting run of automaton A such that the word of the run is not accepted by any of the automata
	 *         B_0,..,B_n. Return null if no such run exists, i.e., the language inclusion A ⊆ B_0 ∪ ... ∪ B_n holds.
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public abstract NestedRun<LETTER, STATE> getCounterexample() throws AutomataOperationCanceledException;

	/**
	 * Add automaton B_{n+1} to our set of subtrahends B_0,...,B_n.
	 *
	 * @param nwa
	 *            subtrahend
	 * @throws AutomataLibraryException
	 *             if construction fails
	 */
	public void addSubtrahend(final INestedWordAutomatonSimple<LETTER, STATE> nwa) throws AutomataLibraryException {
		mNwaB.add(nwa);
	}

	public INestedWordAutomatonSimple<LETTER, STATE> getA() {
		return mNwaA;
	}
}
