/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2009-2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.fair;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.GameGraphChangeType;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.GameGraphChanges;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.relation.Triple;

/**
 * Doc comes later.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 * @param <STATE>
 */
public final class FairGameGraphChanges<LETTER, STATE> extends GameGraphChanges<LETTER, STATE> {
	
	private final NestedMap3<STATE, LETTER, STATE,
		GameGraphChangeType> m_ChangedBuechiTransitions;
	
	public FairGameGraphChanges() {
		super();
		m_ChangedBuechiTransitions =
				new NestedMap3<STATE, LETTER, STATE, GameGraphChangeType>();
	}
	
	public void addedBuechiTransition(final STATE src,
			final LETTER a, final STATE dest) {
		changedBuechiTransition(src, a, dest, GameGraphChangeType.ADDITION);
	}
	
	public NestedMap3<STATE, LETTER, STATE,
		GameGraphChangeType> getChangedBuechiTransitions() {
		return m_ChangedBuechiTransitions;
	}
	
	@Override
	public void merge(final GameGraphChanges<LETTER, STATE> changes,
			final boolean rememberValuesOfFirst) {
		super.merge(changes, rememberValuesOfFirst);
		
		if (changes == null) {
			return;
		}
		
		if (changes instanceof FairGameGraphChanges) {
			FairGameGraphChanges<LETTER, STATE> fairChanges =
					(FairGameGraphChanges<LETTER, STATE>) changes;
			// Merge changed buechi transitions
			NestedMap3<STATE, LETTER, STATE,
			GameGraphChangeType> changedTransitions =
				fairChanges.getChangedBuechiTransitions();
			for (STATE changedKey : changedTransitions.keySet()) {
				for (Triple<LETTER, STATE,
						GameGraphChangeType> changedTrans :
							changedTransitions.get(changedKey).entrySet()) {
					STATE src = changedKey;
					LETTER a = changedTrans.getFirst();
					STATE dest = changedTrans.getSecond();
					GameGraphChangeType changeType =
							m_ChangedBuechiTransitions.get(src, a, dest);
					
					if (changeType == null
							|| changeType.equals(GameGraphChangeType.NO_CHANGE)) {
						// Only add transition change if unknown until now
						m_ChangedBuechiTransitions.put(src, a, dest,
								changedTrans.getThird());
					} else if ((changeType == GameGraphChangeType.ADDITION
							&& changedTrans.getThird() == GameGraphChangeType.REMOVAL)
							|| (changeType == GameGraphChangeType.REMOVAL
							&& changedTrans.getThird() == GameGraphChangeType.ADDITION)) {
						// Nullify change if it was added and then
						// removed or vice versa
						m_ChangedBuechiTransitions.put(src, a, dest,
								GameGraphChangeType.NO_CHANGE);
					}
				}
			}
		}
	}
	
	public void removedBuechiTransition(final STATE src,
			final LETTER a, final STATE dest) {
		changedBuechiTransition(src, a, dest, GameGraphChangeType.REMOVAL);
	}
	
	private void changedBuechiTransition(final STATE src,
			final LETTER a, final STATE dest,
			final GameGraphChangeType type) {
		GameGraphChangeType previousType =
				m_ChangedBuechiTransitions.get(src, a, dest);
		// Nullify change if previously added and then removed or vice versa
		if (previousType != null
				&& ((previousType.equals(GameGraphChangeType.ADDITION)
							&& type.equals(GameGraphChangeType.REMOVAL))
						|| (previousType.equals(GameGraphChangeType.REMOVAL)
							&& type.equals(GameGraphChangeType.ADDITION)))) {
			m_ChangedBuechiTransitions.put(src, a, dest,
					GameGraphChangeType.NO_CHANGE);
		} else {
			m_ChangedBuechiTransitions.put(src, a, dest, type);
		}
	}
}
