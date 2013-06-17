package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker;

import java.util.ArrayList;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.FormulasAndLevelAnnotations;

public class ConcatenationResult {
	public FormulasAndLevelAnnotations formulasAndLvl;
	public ArrayList<HashMap<BoogieVar, Integer>> shiftLevelsForPath;
	
	public ConcatenationResult(FormulasAndLevelAnnotations formulasAndLvl, ArrayList<HashMap<BoogieVar, Integer>> shiftLevelsForPath) {
		assert(formulasAndLvl.size() + 1 == shiftLevelsForPath.size());
		this.formulasAndLvl = formulasAndLvl;
		this.shiftLevelsForPath = shiftLevelsForPath;
	}
}
