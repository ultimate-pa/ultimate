package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.io.PrintWriter;

public class ScopeCmd extends Cmd {
	
	private String m_Cmd;
	private int m_NumScopes, m_LastNumScopes;
	
	public ScopeCmd(String cmd, int numScopes) {
		m_Cmd = cmd;
		m_NumScopes = numScopes;
	}
	
	public boolean isScopeStart() {
		return m_Cmd == "push";
	}

	@Override
	public void dump(PrintWriter out) {
		out.print('(');
		out.print(m_Cmd);
		out.print(' ');
		out.print(m_NumScopes);
		out.println(')');
	}

	public int getNumScopes() {
		return m_NumScopes;
	}

	public void tryNumScopes(int numScopes) {
		m_LastNumScopes = m_NumScopes;
		m_NumScopes = numScopes;
	}
	
	public void reset() {
		m_NumScopes = m_LastNumScopes;
	}
	
	public String toString() {
		return m_Cmd.toUpperCase();
	}

}
