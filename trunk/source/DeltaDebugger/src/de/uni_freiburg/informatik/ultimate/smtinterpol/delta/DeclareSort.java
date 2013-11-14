package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.io.PrintWriter;

public class DeclareSort extends Cmd {
	
	private String m_Sort;
	private int m_Arity;

	public DeclareSort(String sort, int arity) {
		m_Sort = sort;
		m_Arity = arity;
	}
	
	@Override
	public void dump(PrintWriter out) {
		out.print("(declare-sort ");
		out.print(m_Sort);
		out.print(' ');
		out.print(m_Arity);
		out.println(')');
	}

	@Override
	public boolean canBeRemoved() {
		return true;
	}

	@Override
	public boolean hasDefinitions() {
		return true;
	}
	
	public String toString() {
		return "DECLARE_SORT " + m_Sort;
	}

}
