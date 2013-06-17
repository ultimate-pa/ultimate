package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.IAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;

public class IC3Annotation implements IAnnotations {

	private static final long serialVersionUID = 1L;
	private HashMap<String, Object> annotationMap;
	
	public IC3Annotation() {
		annotationMap = new HashMap<String, Object>();
	}
	
	public void setIndex(int index) {
		annotationMap.put("index", index);
	}
	
	public int getIndex() {
		Integer index = (Integer) annotationMap.get("index");
		if (index == null)
			throw new RuntimeException("Index could not be read!");
		return index;
	}
	
	public void setClauseSet(Set<Clause> clauseSet) {
		annotationMap.put("clauseSet", clauseSet);
	}
	
	public Set<Clause> getClauseSet() {
		return (Set<Clause>) annotationMap.get("clauseSet");
	}
	
	public void setLatestLoopLocations(HashMap<CFGExplicitNode, UnwindingNode> loopLocationToArtNode) {
		annotationMap.put("latestLoopLocations", loopLocationToArtNode);
	}
	
	public HashMap<CFGExplicitNode, UnwindingNode> getLatestLoopLocations() {
		return (HashMap<CFGExplicitNode, UnwindingNode>) annotationMap.get("latestLoopLocations");
	}
	
	@Override
	public Map<String, Object> getAnnotationsAsMap() {
		return annotationMap;
	}

}
