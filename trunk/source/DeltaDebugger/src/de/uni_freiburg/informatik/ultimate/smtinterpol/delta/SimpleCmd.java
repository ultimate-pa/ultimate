package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.io.PrintWriter;
import java.util.Map;

/**
 * Represents all commands that do not take any arguments.  These are:
 * - check-sat
 * - get-assertions
 * - get-proof
 * - get-unsat-core
 * - get-model
 * - get-assignment
 * - exit
 * @author Juergen Christ
 */
public class SimpleCmd extends Cmd {
	
	private String m_Cmd;
	
	public SimpleCmd(String cmd) {
		m_Cmd = cmd;
	}

	@Override
	public void dump(PrintWriter out) {
		out.print('(');
		out.print(m_Cmd);
		out.println(')');
	}
	
	public String toString() {
		return m_Cmd.toUpperCase();
	}

	@Override
	public void checkFeature(Map<String, Cmd> features) {
		if (m_Cmd.equals("get-assertions"))
			features.remove(":interactive-mode");
		else if (m_Cmd.equals("get-proof"))
			features.remove(":produce-proofs");
		else if (m_Cmd.equals("get-model"))
			features.remove(":produce-models");
		else if (m_Cmd.equals("get-unsat-core"))
			features.remove(":produce-unsat-cores");
		else if (m_Cmd.equals(":get-assignment"))
			features.remove(":produce-assignments");
	}

}
