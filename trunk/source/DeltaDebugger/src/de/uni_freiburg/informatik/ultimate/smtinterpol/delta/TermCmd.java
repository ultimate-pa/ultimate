package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Super class for all commands containing terms.  This class is needed since
 * a command containing terms might contain named terms and thus provide
 * definitions of new symbols.
 * @author Juergen Christ
 */
public abstract class TermCmd extends Cmd {

	private boolean m_HasNames = false;
	
	protected void addTerm(Term t) {
		m_HasNames |= new NamedHelper().checkTerm(t);
	}
	
	protected void addTerms(Term[] ts) {
		NamedHelper nh = new NamedHelper();
		for (int i = 0; i < ts.length && !m_HasNames; ++i)
			m_HasNames |= nh.checkTerm(ts[i]);
	}

	@Override
	public boolean hasDefinitions() {
		return m_HasNames;
	}

}
