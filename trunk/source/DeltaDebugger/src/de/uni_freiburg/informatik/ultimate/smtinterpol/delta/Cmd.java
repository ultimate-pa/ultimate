package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.io.PrintWriter;
import java.util.Map;
import java.util.Set;

public abstract class Cmd {
	
	private boolean m_Active = true;
	
	public void activate() {
		m_Active = true;
	}
	
	public void deactivate() {
		m_Active = false;
	}
	
	public boolean isActive() {
		return m_Active;
	}
	
	public boolean canBeRemoved() {
		return true;
	}
	
	public abstract void dump(PrintWriter out);
	
	public boolean hasDefinitions() {
		return false;
	}
	
	public void insertDefinitions(Map<String, Cmd> context) {}
	
	public void addUsedDefinitions(Map<String, Cmd> context, Set<Cmd> usedDefs) {}
	
	public String provideFeature() {
		return null;
	}
	
	public void checkFeature(Map<String, Cmd> features) {}
	
}
