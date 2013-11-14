package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.io.PrintWriter;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class GetInterpolants extends Cmd {
	
	private Term[] m_Partition, m_OldPartition;
	private int[] m_Sos, m_OldSos;
	
	public GetInterpolants(Term[] partition, int[] sos) {
		m_Partition = partition;
		m_Sos = sos;
	}

	@Override
	public void dump(PrintWriter out) {
		// Copied from LoggingScript...
		out.print("(get-interpolants ");
		PrintTerm pt = new PrintTerm();
		pt.append(out, m_Partition[0]);
		for (int i = 1; i < m_Partition.length; ++i) {
			int prevStart = m_Sos[i - 1];
			while (m_Sos[i] < prevStart) {
				out.print(')');
				prevStart = m_Sos[prevStart - 1];
			}
			out.print(' ');
			if (m_Sos[i] == i)
				out.print('(');
			pt.append(out, m_Partition[i]);
		}
		out.println(')');
	}
	
	public Term[] getPartition() {
		return m_Partition;
	}
	public int[] getStartOfSubtree() {
		return m_Sos;
	}
	
	public void setNewPartition(Term[] newPartition) {
		m_OldPartition = m_Partition;
		m_Partition = newPartition;
	}
	public void setNewStartOfSubtree(int[] newSos) {
		m_OldSos = m_Sos;
		m_Sos = newSos;
	}
	
	public void failure() {
		m_Partition = m_OldPartition;
		m_Sos = m_OldSos;
	}
	public void success() {
		System.err.println("New partition: " + java.util.Arrays.toString(m_Partition));
		m_OldPartition = null;
		m_OldSos = null;
	}
	
	public String toString() {
		return "GET_INTERPOLANTS";
	}

	@Override
	public void checkFeature(Map<String, Cmd> features) {
		features.remove(":produce-interpolants");
	}

}
