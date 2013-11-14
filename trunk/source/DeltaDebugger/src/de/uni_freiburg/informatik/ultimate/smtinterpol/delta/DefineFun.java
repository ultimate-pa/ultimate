package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.io.PrintWriter;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class DefineFun extends AbstractOneTermCmd {
	
	private String m_Fun;
	private TermVariable[] m_Params;
	private Sort m_ResultSort;
	
	public DefineFun(String fun, TermVariable[] params, Sort resultSort,
			Term definition) {
		super(definition);
		m_Fun = fun;
		m_Params = params;
		m_ResultSort = resultSort;
	}

	@Override
	public void dump(PrintWriter out) {
		super.dump(out);
		out.print("(define-fun ");
		out.print(m_Fun);
		out.print(" (");
		for (TermVariable tv : m_Params) {
			out.print('(');
			out.print(tv.getName());
			out.print(' ');
			out.print(tv.getSort());
			out.print(')');
		}
		out.print(") ");
		out.print(m_ResultSort);
		out.print(' ');
		new PrintTerm().append(out, m_Term);
		out.println(')');
	}

	@Override
	public void insertDefinitions(Map<String, Cmd> context) {
		context.put(m_Fun, this);
	}
	
	public String toString() {
		return "DEFINE_FUN " + m_Fun;
	}
	
}
