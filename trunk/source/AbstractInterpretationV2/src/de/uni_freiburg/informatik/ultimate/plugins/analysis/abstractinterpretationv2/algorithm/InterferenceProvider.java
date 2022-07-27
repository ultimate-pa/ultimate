/*
 * Copyright (C) 2022 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;

/**
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 * @param <STATE>
 */
public class InterferenceProvider<ACTION, STATE extends IAbstractState<STATE>> {
	private final Map<ACTION, DisjunctiveAbstractState<STATE>> mInterferingStates;
	private final Set<ACTION> mReadsFromOwnThread;

	public InterferenceProvider(final Map<ACTION, DisjunctiveAbstractState<STATE>> interferingStates,
			final Set<ACTION> readsFromOwnThread) {
		mInterferingStates = interferingStates;
		mReadsFromOwnThread = readsFromOwnThread;
	}

	public InterferenceProvider() {
		this(Map.of(), Set.of());
	}

	public DisjunctiveAbstractState<STATE> getInterferingState(final ACTION action) {
		return mInterferingStates.get(action);
	}

	public boolean canReadFromOwnThread(final ACTION action) {
		return mReadsFromOwnThread.contains(action);
	}
}
