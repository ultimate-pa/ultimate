package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.io.PrintWriter;

import de.uni_freiburg.informatik.ultimate.logic.Logics;

public class SetLogic extends Cmd {
	
	private Logics m_logic;
	
	public SetLogic(Logics logic) {
		m_logic = logic;
	}

	@Override
	public void dump(PrintWriter out) {
		out.print("(set-logic ");
		out.print(m_logic.name());
		out.println(')');
	}

	@Override
	public boolean canBeRemoved() {
		// Never remove set-logic!!!
		return false;
	}
	
	public String toString() {
		return "SET_LOGIC";
	}

}
