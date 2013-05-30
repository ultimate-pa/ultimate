package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi;

import java.text.MessageFormat;

import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;

public interface IOpWithDelayedDeadEndRemoval<LETTER, STATE> {
	
	public Iterable<UpDownEntry<STATE>> getRemovedUpDownEntry();
	
	public boolean removeDeadEnds();
	
	public INestedWordAutomatonOldApi<LETTER,STATE> getResult() throws OperationCanceledException;
	
	public long getDeadEndRemovalTime();
	
	
	public class UpDownEntry<STATE> {
		private final STATE m_Up;
		private final STATE m_Down;
		private final STATE m_Entry;
		
		public UpDownEntry(STATE up, STATE down, STATE entry) {
			m_Up = up;
			m_Down = down;
			m_Entry = entry;
		}
		public STATE getUp() {
			return m_Up;
		}
		public STATE getDown() {
			return m_Down;
		}
		public STATE getEntry() {
			return m_Entry;
		}
		
		@Override
		public String toString() {
			return MessageFormat.format("up: {0} down: {1} entry {2}", m_Up, m_Down, m_Entry);
		}
		
		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result
					+ ((m_Down == null) ? 0 : m_Down.hashCode());
			result = prime * result
					+ ((m_Entry == null) ? 0 : m_Entry.hashCode());
			result = prime * result + ((m_Up == null) ? 0 : m_Up.hashCode());
			return result;
		}
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			UpDownEntry other = (UpDownEntry) obj;
			if (m_Down == null) {
				if (other.m_Down != null)
					return false;
			} else if (!m_Down.equals(other.m_Down))
				return false;
			if (m_Entry == null) {
				if (other.m_Entry != null)
					return false;
			} else if (!m_Entry.equals(other.m_Entry))
				return false;
			if (m_Up == null) {
				if (other.m_Up != null)
					return false;
			} else if (!m_Up.equals(other.m_Up))
				return false;
			return true;
		}
	}

}
