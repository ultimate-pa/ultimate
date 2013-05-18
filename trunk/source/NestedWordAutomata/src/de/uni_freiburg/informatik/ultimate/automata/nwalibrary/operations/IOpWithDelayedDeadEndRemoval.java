package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

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
	}

}
