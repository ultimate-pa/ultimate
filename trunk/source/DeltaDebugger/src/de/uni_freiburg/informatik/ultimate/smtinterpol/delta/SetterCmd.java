package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.io.PrintWriter;


public class SetterCmd extends Cmd {
	
	private String m_Cmd;
	private boolean m_CanBeRemoved;
	private String m_Key;
	private Object m_Val;
	
	public SetterCmd(String cmd, String key, Object val) {
		m_Cmd = cmd;
		// Remove most infos but keep options...
		/* This strategy might be bad if proof production is enabled but the
		 * error does not depend on a proof.  Maybe we should implement a
		 * feature collection...
		 */
		boolean isInfo = cmd == "set-info";
		m_CanBeRemoved = !((isInfo && key.equals(":error-behavior")) ||
				(!isInfo && (key.startsWith(":produce-") || 
						key.endsWith("-check-mode"))));
		m_Key = key;
		m_Val = val;
		
	}

	@Override
	public boolean canBeRemoved() {
		return m_CanBeRemoved;
	}

	@Override
	public void dump(PrintWriter out) {
		out.print('(');
		out.print(m_Cmd);
		out.print(' ');
		out.print(m_Key);
		out.print(' ');
		out.print(m_Val);
		out.println(')');
	}
	
	public String toString() {
		return m_Cmd.toUpperCase();
	}

	@Override
	public String provideFeature() {
		return m_Cmd == "set-option" ? m_Key : null;
	}

}
