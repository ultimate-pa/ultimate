package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.io.PrintWriter;

import de.uni_freiburg.informatik.ultimate.logic.Sort;

public class DefineSort extends Cmd {
	
	private String m_Sort;
	private Sort[] m_Params;
	private Sort m_Definition;
	
	public DefineSort(String sort, Sort[] params, Sort definition) {
		m_Sort = sort;
		m_Params = params;
		m_Definition = definition;
	}

	@Override
	public void dump(PrintWriter out) {
		out.print("(define-sort ");
		out.print(m_Sort);
		out.print(" (");
		String sep = "";
		for (Sort p : m_Params) {
			out.print(sep);
			out.print(p.getName());
			sep = " ";
		}
		out.print(") ");
		out.print(m_Definition);
		out.println(')');
	}

	@Override
	public boolean hasDefinitions() {
		return true;
	}
	
	public String toString() {
		return "DEFINE_SORT " + m_Sort;
	}

}
