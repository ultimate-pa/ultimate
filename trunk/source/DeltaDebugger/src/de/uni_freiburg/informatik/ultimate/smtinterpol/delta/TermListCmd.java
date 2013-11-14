package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.io.PrintWriter;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Represents all commands that take a list of terms.  These are:
 * - get-value
 * - check-allsat
 * @author Juergen Christ
 */
public class TermListCmd extends TermCmd {
	
	private String m_Cmd;
	private Term[] m_List, m_OldList;
	
	public TermListCmd(String cmd, Term[] list) {
		m_Cmd = cmd;
		m_List = list;
		addTerms(list);
	}

	@Override
	public void dump(PrintWriter out) {
		out.print('(');
		out.print(m_Cmd);
		out.print(" (");
		PrintTerm pt = new PrintTerm();
		String sep = "";
		for (Term t : m_List) {
			out.print(sep);
			pt.append(out, t);
			sep = " ";
		}
		out.println("))");
	}


	@Override
	public void insertDefinitions(Map<String, Cmd> context) {
		NamedHelper nh = new NamedHelper();
		for (Term t : m_List)
			nh.addNames(t, context, this);
	}

	@Override
	public void addUsedDefinitions(Map<String, Cmd> context, Set<Cmd> usedDefs) {
		DefinitionTracker dt = new DefinitionTracker(context, usedDefs);
		for (Term t : m_List)
			dt.track(t);
	}

	public Term[] getTerms() {
		return m_List;
	}
	
	public void setNewTerms(Term[] newTerms) {
		m_OldList = m_List;
		m_List = newTerms;
	}
	
	public void failure() {
		m_List = m_OldList;
	}
	
	public void success() {
		m_OldList = null;
	}
	
	public String toString() {
		return m_Cmd.toUpperCase();
	}

	@Override
	public void checkFeature(Map<String, Cmd> features) {
		if (m_Cmd.equals("get-value"))
			features.remove(":produce-models");
	}

}
