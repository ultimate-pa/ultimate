package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.io.PrintWriter;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;

public class DeclareFun extends Cmd {

	private String m_Fun;
	private Sort[] m_Params;
	private Sort m_ResultSort;
	
	public DeclareFun(String fun, Sort[] params, Sort resultSort) {
		m_Fun = fun;
		m_Params = params;
		m_ResultSort = resultSort;
	}
	
	@Override
	public void dump(PrintWriter out) {
		out.print("(declare-fun ");
		out.print(PrintTerm.quoteIdentifier(m_Fun));
		out.print(" (");
		String sep = "";
		for (Sort p : m_Params) {
			out.print(sep);
			out.print(p);
			sep = " ";
		}
		out.print(") ");
		out.print(m_ResultSort);
		out.println(')');
	}

	@Override
	public boolean hasDefinitions() {
		return true;
	}

	@Override
	public void insertDefinitions(Map<String, Cmd> context) {
		context.put(m_Fun, this);
	}
	
	public String toString() {
		return "DECLARE_FUN " + m_Fun;
	}
	
}
