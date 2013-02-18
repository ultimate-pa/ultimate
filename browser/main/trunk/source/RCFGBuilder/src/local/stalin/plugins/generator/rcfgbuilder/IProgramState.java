package local.stalin.plugins.generator.rcfgbuilder;

import java.util.Map;
import java.util.Set;

import local.stalin.logic.ApplicationTerm;
import local.stalin.logic.Formula;

public interface IProgramState {
	
	public ProgramPoint getProgramPoint();
	
	public Set<String> getVars();
	
	public Set<String> getOldVars();
	
	public Formula getFormula();
	
	public boolean isTrue();
	
	public boolean isFalse();
	
	public boolean isUnknown();
	
	public Set<IProgramState> getConjunction();
}
