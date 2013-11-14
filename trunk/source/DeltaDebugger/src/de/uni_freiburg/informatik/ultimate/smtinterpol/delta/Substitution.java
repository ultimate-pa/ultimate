package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import de.uni_freiburg.informatik.ultimate.logic.Term;

public abstract class Substitution {
	
	private boolean m_Active = false;
	private Term m_Match;
	private boolean m_Success = false;
	
	public Substitution(Term match) {
		m_Match = match;
	}
	
	public boolean matches(Term t) {
		return m_Match == t;
	}
	
	public Term getMatch() {
		return m_Match;
	}
	
	public boolean isActive() {
		return m_Active;
	}
	
	public void activate() {
		m_Active = true;
	}
	
	public void deactivate() {
		m_Active = false;
	}
	
	public void success() {
		m_Success = true;
	}
	
	public boolean isSuccess() {
		return m_Success;
	}
	
	public abstract Term apply(Term input);
	public abstract Cmd getAdditionalCmd(Term input);
}