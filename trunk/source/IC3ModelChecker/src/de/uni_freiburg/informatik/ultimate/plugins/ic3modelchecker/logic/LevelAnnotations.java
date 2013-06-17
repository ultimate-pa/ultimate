package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SMTEdgeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SMTNodeAnnotations;

/** Contains information about variables in a formula (if they are inVars / outVars, script...). */
public class LevelAnnotations {
	private Script script;
	private HashMap<Integer, HashMap<BoogieVar, TermVariable>> leveledVars;
	private HashSet<TermVariable> allVars;
	
	public LevelAnnotations() {
		this.leveledVars = new HashMap<Integer, HashMap<BoogieVar, TermVariable>>();
		this.allVars = new HashSet<TermVariable>();
	}
	
	public LevelAnnotations(Script script) {
		this();
		this.script = script;
	}
	
	public LevelAnnotations(SMTEdgeAnnotations edgeAnnotations, SMTNodeAnnotations nodeAnnotations) {
		this();
		assert((edgeAnnotations != null) != (nodeAnnotations != null));
		if (edgeAnnotations != null)
			extractFromSmtEdgeAnnotations(edgeAnnotations);
		else if (nodeAnnotations != null)
			extractFromSmtNodeAnnotations(nodeAnnotations);
		assert(this.getScript() != null);
	}
	
	public LevelAnnotations(Script script, HashSet<TermVariable> allVars, HashMap<BoogieVar, TermVariable> inVars,
							HashMap<BoogieVar, TermVariable> outVars) {
		this();
		this.script = script;
		this.allVars = allVars;
		leveledVars.put(0, inVars);
		leveledVars.put(1, outVars);
	}
	
	public LevelAnnotations(Script script, HashSet<TermVariable> allVars, HashMap<Integer, HashMap<BoogieVar, TermVariable>> leveledVars) {
		this.script = script;
		this.allVars = allVars;
		this.leveledVars = leveledVars;
	}
	
	
	
	private void extractFromSmtEdgeAnnotations(SMTEdgeAnnotations edgeSmt) {
		this.script = edgeSmt.getScript();
		allVars.addAll(edgeSmt.getVars());
		HashMap<BoogieVar, TermVariable> levelZero = getOrCreateLevel(0);
		levelZero.putAll(edgeSmt.getInVars());
		HashMap<BoogieVar, TermVariable> levelOne = getOrCreateLevel(1);
		levelOne.putAll(edgeSmt.getOutVars());
	}
	
	public SMTEdgeAnnotations extractToSmtEdgeAnnotations() {
		SMTEdgeAnnotations result = new SMTEdgeAnnotations();
		result.setScript(script);
		result.setVars(allVars);
		result.setInVars(getOrCreateLevel(0));
		result.setOutVars(getOrCreateLevel(1));
		return result;
	}
	
	private void extractFromSmtNodeAnnotations(SMTNodeAnnotations nodeSmt) {
		this.script = nodeSmt.getScript();
		allVars.addAll(nodeSmt.getVars());
		HashMap<BoogieVar, TermVariable> levelZero = getOrCreateLevel(0);
		levelZero.putAll(nodeSmt.getInVars());
	}
	
	public HashMap<BoogieVar, TermVariable> getOrCreateLevel(int level) {
		HashMap<BoogieVar, TermVariable> result = leveledVars.get(level);
		if (result == null) {
			result = new HashMap<BoogieVar, TermVariable>();
			leveledVars.put(level, result);
		}
		return result;
	}
	
	public Script getScript() {
		return this.script;
	}
	
	public void setScript(Script script) {
		this.script = script;
	}
	
	public HashMap<Integer, HashMap<BoogieVar, TermVariable>> getLeveledVars() {
		return leveledVars;
	}
	
	public HashMap<BoogieVar, TermVariable> getLevel(int level) {
		return leveledVars.get(level);
	}
	
	public TreeSet<Integer> getAvailableLevels() {
		return new TreeSet<Integer>(leveledVars.keySet());
	}
	
	public HashMap<BoogieVar, TermVariable> getInVars() {
		return getOrCreateLevel(0);
	}
	
	public HashMap<BoogieVar, TermVariable> getOutVars() {
		return getOrCreateLevel(1);
	}
	
	public HashSet<TermVariable> getVars() {
		return allVars;
	}
	
	public HashSet<BoogieVar> getAllBoogieVars() {
		HashSet<BoogieVar> result = new HashSet<>();
		for (int level : getAvailableLevels()) {
			result.addAll(getLevel(level).keySet());
		}
		return result;
	}
	
	public BoogieVar getBoogieVar(TermVariable termVar) {
		for (int level : getAvailableLevels()) {
			HashMap<BoogieVar, TermVariable> varsOfLevel = getLevel(level);
			for (BoogieVar boogieVar : varsOfLevel.keySet()) {
				if (varsOfLevel.get(boogieVar).equals(termVar))
					return boogieVar;
			}
		}
		return null;
	}
	
	public HashSet<TermVariable> getAllUnleveledVars() {
		HashSet<TermVariable> result = new HashSet<TermVariable>();
		for (TermVariable termVar : allVars) {
			if (getBoogieVar(termVar) == null)
				result.add(termVar);
		}
		return result;
	}
	
	/** deep copy */
	public LevelAnnotations clone() {
		HashSet<TermVariable> newAllVars = new HashSet<>(allVars);
		HashMap<Integer, HashMap<BoogieVar, TermVariable>> newLeveledVars = new HashMap<Integer, HashMap<BoogieVar, TermVariable>>();
		for (Integer level : leveledVars.keySet()) {
			HashMap<BoogieVar, TermVariable> varsOfLevel = leveledVars.get(level);
			HashMap<BoogieVar, TermVariable> newVarsOfLevel = new HashMap<BoogieVar, TermVariable>();
			newVarsOfLevel.putAll(varsOfLevel);
			newLeveledVars.put(level, newVarsOfLevel);
		}
		return new LevelAnnotations(script, newAllVars, newLeveledVars);
	}
	
	public static LevelAnnotations getMerged(List<LevelAnnotations> levelAnnotationList, Term checkAgainst) {
		if (levelAnnotationList.isEmpty()) return null;
		Script script = levelAnnotationList.get(0).getScript();
		LevelAnnotations result = new LevelAnnotations();
		result.setScript(script);
		
		HashSet<TermVariable> resultAllVars = result.getVars();
		for (LevelAnnotations levelAnnotation : levelAnnotationList) {
			resultAllVars.addAll(levelAnnotation.getVars());
			
			for (Integer level : levelAnnotation.getAvailableLevels()) {
				HashMap<BoogieVar, TermVariable> varsOfLevel = levelAnnotation.getLevel(level);
				HashMap<BoogieVar, TermVariable> resultVarsOfLevel = result.getOrCreateLevel(level);
				resultVarsOfLevel.putAll(varsOfLevel);
			}
		}
		if (checkAgainst != null) {
			result.reduceLevelAnnotations(checkAgainst);
		}
		
		return result;
	}
	
	/** Reduces to those variables appearing in given formula. Modifies this. */
	public void reduceLevelAnnotations(Term checkAgainst) {
		HashSet<TermVariable> existingVars = new HashSet<TermVariable>(Arrays.asList(checkAgainst.getFreeVars()));
		allVars.retainAll(existingVars);
		for (Integer level : this.getAvailableLevels()) {
			HashMap<BoogieVar, TermVariable> varsOfLevel = this.getOrCreateLevel(level);
			varsOfLevel.values().retainAll(existingVars);
			if (varsOfLevel.isEmpty()) // some cleaning
				leveledVars.remove(level);
		}
	}
	
	@Override
	public String toString() {
		return "leveledVars: "+leveledVars+"; allVars: "+allVars;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((allVars == null) ? 0 : allVars.hashCode());
		result = prime * result
				+ ((leveledVars == null) ? 0 : leveledVars.hashCode());
		result = prime * result + ((script == null) ? 0 : script.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		LevelAnnotations other = (LevelAnnotations) obj;
		if (allVars == null) {
			if (other.allVars != null)
				return false;
		} else if (!allVars.equals(other.allVars))
			return false;
		if (leveledVars == null) {
			if (other.leveledVars != null)
				return false;
		} else if (!leveledVars.equals(other.leveledVars))
			return false;
		if (script == null) {
			if (other.script != null)
				return false;
		} else if (!script.equals(other.script))
			return false;
		return true;
	}
}
