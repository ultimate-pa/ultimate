package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.transfomers.SubstituteTermTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.FormulaAndLevelAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.LevelAnnotations;

// Shifting notation of variable names like this: xIn3 > xIn2 > xIn > xOut > xOut2 > xOut3 

public class SubstitutionManager {
	private static Sort[] emptySort = new Sort[0];
	
	
	
	/** Please call push() beforehand and pop() afterwards.<br/>
	 * Replaces all free variables of given term by freshly declared constant symbols with the same name. If a substitution map is given,
	 * uses that as basis and doesn't declare already declared variables. Note that the returned substitution map will fully contain the given one. */
	public static ConstSubstResult substituteFreeVarsToConst(Script script, Term formula, HashMap<Term, Term> alreadyDeclared) {
		HashSet<TermVariable> freeVars = new HashSet<TermVariable>(Arrays.asList(formula.getFreeVars()));
		ConstSubstResult result = substituteVarsToConst(script, formula, freeVars, alreadyDeclared);
		return result;
	}
	
	public static ConstSubstResult substituteVarsToConst(Script script, Term formula, Set<TermVariable> varsToReplace, HashMap<Term, Term> alreadyDeclared) {
		SubstituteTermTransformer subst = new SubstituteTermTransformer();
		HashMap<Term, Term> substMap;
		HashSet<TermVariable> varsToDeclare = new HashSet<TermVariable>(varsToReplace);
		if (alreadyDeclared != null) {
			varsToDeclare.removeAll(alreadyDeclared.keySet());
			substMap = new HashMap<Term, Term>(alreadyDeclared);
		} else {
			substMap = new HashMap<Term, Term>();
		}
		
		for (TermVariable var : varsToDeclare) {
			String constName = var.getName();
			script.declareFun(constName, emptySort, var.getSort());
			Term newConstantVar = script.term(constName);
			substMap.put(var, newConstantVar);
		}
		Term substTerm = subst.substitute(formula, (HashMap<Term, Term>)substMap);
		ConstSubstResult result = new ConstSubstResult(substMap, substTerm);
		return result;
	}
	
	
	/** Replaces all vars by specially named TermVariables.
	 * Doesn't create constants needed for satisfiability check (use substituteFreeVarsToConst for that). Pure. */
	public static FormulaAndLevelAnnotation substituteInOut(Script script, FormulaAndLevelAnnotation formulaAndLvl) {
		// Replace all leveled vars:
		FormulaAndLevelAnnotation result = substituteSpecificInToOut(script, formulaAndLvl, 0, true);
		return result;
	}
	
	
	/** TermVariable name shifting with specific shift levels for each variable.
	 * If forceRenameAll is set, every variable will be renamed to a proper name.
	 * Pure. */
	public static FormulaAndLevelAnnotation substituteSpecificInToOut(Script script,
												FormulaAndLevelAnnotation formulaAndLvl, 
												HashMap<BoogieVar, Integer> shiftLevelsPerVar, boolean forceRenameAll) {
		Term formula = formulaAndLvl.getFormula();
		LevelAnnotations levelAnnotation = formulaAndLvl.getLevelAnnotation();
		SubstituteTermTransformer subst = new SubstituteTermTransformer();
		HashMap<Term, Term> formulaSubstMap = new HashMap<Term, Term>();
		
		LevelAnnotations newLevelAnnotation = new LevelAnnotations();
		newLevelAnnotation.setScript(script);
		HashSet<TermVariable> newAllVars = newLevelAnnotation.getVars();
		
		// Treatment of multiple termVars with same name:
		// Only the termVar with the minimum level is kept, the others are
		// removed and won't be shifted.
		HashSet<TermVariable> alreadySeenTermVars = new HashSet<TermVariable>();
		
		for (Integer level : levelAnnotation.getAvailableLevels()) {
			HashMap<BoogieVar, TermVariable> varsOfLevel = levelAnnotation.getLevel(level);
			Iterator<BoogieVar> boogieVarIterator = varsOfLevel.keySet().iterator();
			while (boogieVarIterator.hasNext()) {
				BoogieVar boogieVar = boogieVarIterator.next();
				TermVariable termVar = varsOfLevel.get(boogieVar);
				if (alreadySeenTermVars.contains(termVar))
					continue;
				alreadySeenTermVars.add(termVar);
				// Look up from given shiftLevels how this var should be renamed
				Integer deltaShiftLevel = shiftLevelsPerVar.get(boogieVar);
				if (!forceRenameAll) {
					if (deltaShiftLevel != null && deltaShiftLevel != 0) {
						String newTermVarName = shiftVarname(boogieVar, level, deltaShiftLevel);
						TermVariable newTermVar = script.variable(newTermVarName, termVar.getDeclaredSort());
						int newLevel = level+deltaShiftLevel;
						newLevelAnnotation.getOrCreateLevel(newLevel).put(boogieVar, newTermVar);
						newAllVars.add(newTermVar);
						formulaSubstMap.put(termVar, newTermVar);
					} else {
						// No shifting specified: Just pass the old entries into the new level annotation
						newLevelAnnotation.getOrCreateLevel(level).put(boogieVar, termVar);
						newAllVars.add(termVar);
					}
				} else {
					// Force rename
					if (deltaShiftLevel == null)
						deltaShiftLevel = 0;
					String newTermVarName = shiftVarname(boogieVar, level, deltaShiftLevel);
					TermVariable newTermVar = script.variable(newTermVarName, termVar.getDeclaredSort());
					int newLevel = level+deltaShiftLevel;
					newLevelAnnotation.getOrCreateLevel(newLevel).put(boogieVar, newTermVar);
					newAllVars.add(newTermVar);
					formulaSubstMap.put(termVar, newTermVar);
				}
			}
		}
		// Now treat all remaining unleveled term vars 
		HashSet<TermVariable> unseenVars = new HashSet<TermVariable>(levelAnnotation.getVars());
		unseenVars.removeAll(alreadySeenTermVars);
		for (TermVariable unseenVar : unseenVars) {
			if (forceRenameAll) {
				String newVarname = unseenVar.getName(); //.replaceAll("_", "");
				TermVariable newTermVar = script.variable(newVarname, unseenVar.getSort());
				formulaSubstMap.put(unseenVar, newTermVar);
				newAllVars.add(newTermVar);
			} else {
				newAllVars.add(unseenVar);
			}
		}
		if (forceRenameAll)
			assert(formulaSubstMap.keySet().containsAll(Arrays.asList(formula.getFreeVars())));

		Term substFormula = subst.substitute(formula, formulaSubstMap);
		return new FormulaAndLevelAnnotation(substFormula, newLevelAnnotation);
	}
	/** TermVariable name shifting for a given subset of variables and common shift level.
	 * If forceRenameAll is set, every variable will be renamed to a proper name.
	 * Pure. */
	public static FormulaAndLevelAnnotation substituteSpecificInToOut(Script script,
												FormulaAndLevelAnnotation formulaAndLevel,
												HashSet<BoogieVar> varsToShift, int level, boolean forceRenameAll) {
		HashMap<BoogieVar, Integer> shiftLevelsPerVar = new HashMap<>();
		for (BoogieVar boogieVar : varsToShift) {
			shiftLevelsPerVar.put(boogieVar, level);
		}
		return substituteSpecificInToOut(script, formulaAndLevel, shiftLevelsPerVar, forceRenameAll);
	}
	/** TermVariable name shifting for all variables by a common shift level.
	 * If forceRenameAll is set, every variable will be renamed to a proper name.
	 * Pure. */
	public static FormulaAndLevelAnnotation substituteSpecificInToOut(Script script,
												FormulaAndLevelAnnotation formulaAndLvl,
												int level, boolean forceRenameAll) {
		LevelAnnotations levelAnnotation = formulaAndLvl.getLevelAnnotation();
		HashSet<BoogieVar> varsToShift = new HashSet<>();
		varsToShift.addAll(levelAnnotation.getAllBoogieVars());
		return substituteSpecificInToOut(script, formulaAndLvl, varsToShift, level, forceRenameAll);
	}
	
	/** Determines the shifted TermVariable name from its BoogieVar.
	 * Pure. */
	public static String shiftVarname(BoogieVar boogieVar, int originalShiftLevel, int deltaShiftLevel) {
		
		String safeBoogieName = boogieVar.getIdentifier(); //.replaceAll("_", "");
		int targetLevel = originalShiftLevel + deltaShiftLevel;
		if (targetLevel < 0)
			return safeBoogieName+Settings.levelSuffix+Settings.minusSuffix+(-targetLevel);
		else
			return safeBoogieName+Settings.levelSuffix+targetLevel;
	}
	
	
	
	public static void printSubstMap(HashMap<Term, Term> substMap) {
		for (Entry<Term, Term> entry : substMap.entrySet()) {
			TreeIC3.logger().debug(entry.getKey()+"\t->\t"+entry.getValue());
		}
	}
}
