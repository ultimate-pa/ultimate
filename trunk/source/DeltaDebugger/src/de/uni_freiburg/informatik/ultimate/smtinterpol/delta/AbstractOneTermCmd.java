package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.io.PrintWriter;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Term;

public abstract class AbstractOneTermCmd extends TermCmd {

	protected Term m_Term;
	private Term m_OldTerm;
	protected List<Cmd> m_PreCmds;
	
	protected AbstractOneTermCmd(Term term) {
		m_Term = term;
		addTerm(term);
	}
	
	public Term getTerm() {
		return m_Term;
	}
	
	public void setTerm(Term newTerm) {
		m_OldTerm = m_Term;
		m_Term = newTerm;
	}
	
	public void success() {
		m_OldTerm = null;
	}
	
	public void failure() {
		m_Term = m_OldTerm;
	}

	public void appendPreCmds(List<Cmd> pres) {
		if (pres == null || pres.isEmpty())
			return;
		if (m_PreCmds == null)
			m_PreCmds = pres;
		else
			m_PreCmds.addAll(pres);
	}
	
	public void removePreCmds(List<Cmd> pres) {
		if (pres == null || pres.isEmpty())
			return;
		m_PreCmds.removeAll(pres);
		if (m_PreCmds.isEmpty())
			m_PreCmds = null;
	}

	@Override
	public void dump(PrintWriter out) {
		if (m_PreCmds != null)
			for (Cmd cmd : m_PreCmds)
				cmd.dump(out);
	}

}
