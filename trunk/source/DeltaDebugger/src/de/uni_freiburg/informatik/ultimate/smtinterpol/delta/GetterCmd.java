package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.io.PrintWriter;

/**
 * Represents get-info and get-option commands
 * @author Juergen Christ
 */
public class GetterCmd extends Cmd {

	private String m_Cmd;
	private String m_Key;
	
	public GetterCmd(String cmd, String key) {
		m_Cmd = cmd;
		m_Key = key;
	}
	
	@Override
	public void dump(PrintWriter out) {
		out.print('(');
		out.print(m_Cmd);
		out.print(' ');
		out.print(m_Key);
		out.println(')');
	}
	
	public String toString() {
		return m_Cmd.toUpperCase();
	}

}
