/*
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi;

import java.text.MessageFormat;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;

/**
 * Interface for operations with delayed dead end removal.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public interface IOpWithDelayedDeadEndRemoval<LETTER, STATE> {
	/**
	 * @return Removed up-down entries.
	 */
	Iterable<UpDownEntry<STATE>> getRemovedUpDownEntry();

	/**
	 * Removes dead ends.
	 * 
	 * @return {@code true} iff states were removed
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	boolean removeDeadEnds() throws AutomataOperationCanceledException;

	/**
	 * @return The operation result.
	 */
	INestedWordAutomaton<LETTER, STATE> getResult();

	/**
	 * @return The time it took to remove the dead ends.
	 */
	long getDeadEndRemovalTime();

	/**
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 * @param <STATE>
	 *            state type
	 */
	public class UpDownEntry<STATE> {
		private final STATE mUp;
		private final STATE mDown;
		private final STATE mEntry;

		/**
		 * Constructor.
		 * 
		 * @param upState
		 *            up state
		 * @param downState
		 *            dow state
		 * @param entry
		 *            entry
		 */
		public UpDownEntry(final STATE upState, final STATE downState, final STATE entry) {
			mUp = upState;
			mDown = downState;
			mEntry = entry;
		}

		public STATE getUp() {
			return mUp;
		}

		public STATE getDown() {
			return mDown;
		}

		public STATE getEntry() {
			return mEntry;
		}

		@Override
		public String toString() {
			return MessageFormat.format("up: {0} down: {1} entry {2}", mUp, mDown, mEntry);
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = prime + ((mDown == null) ? 0 : mDown.hashCode());
			result = prime * result + ((mEntry == null) ? 0 : mEntry.hashCode());
			result = prime * result + ((mUp == null) ? 0 : mUp.hashCode());
			return result;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null || getClass() != obj.getClass()) {
				return false;
			}
			final UpDownEntry<?> other = (UpDownEntry<?>) obj;
			if (mDown == null) {
				if (other.mDown != null) {
					return false;
				}
			} else if (!mDown.equals(other.mDown)) {
				return false;
			}
			if (mEntry == null) {
				if (other.mEntry != null) {
					return false;
				}
			} else if (!mEntry.equals(other.mEntry)) {
				return false;
			}
			if (mUp == null) {
				if (other.mUp != null) {
					return false;
				}
			} else if (!mUp.equals(other.mUp)) {
				return false;
			}
			return true;
		}
	}
}
