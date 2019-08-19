/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Provides GlobalVarsAssignment and OldVarsAssignment.
 * @author Matthias Heizmann
 */
public class OldVarsAssignmentCache {
	
	
	protected final ManagedScript mMgdScript;
	
	private final ModifiableGlobalsTable mModifiableGlobalsTable;
	
	private final Map<String, UnmodifiableTransFormula> mProc2OldVarsAssignment;
	private final Map<String, UnmodifiableTransFormula> mProc2GlobalVarsAssignment;
	
	
	public OldVarsAssignmentCache(final ManagedScript mgdScript, final ModifiableGlobalsTable modifiableGlobalsTable) {
		mMgdScript = mgdScript;
		mModifiableGlobalsTable = modifiableGlobalsTable;
		mProc2OldVarsAssignment = new HashMap<>();
		mProc2GlobalVarsAssignment = new HashMap<>();
	}
	
	
	/**
	 * Returns a TransFormula that represents an assignment 
	 * gOld_1,...,gOld_n :=g_1,...,g_n
	 * where g_1,...,g_n are the global variables that can be modified by
	 * procedure proc and gOld_1,...,gOld_n are the corresponding oldvars.
	 */
	public UnmodifiableTransFormula getOldVarsAssignment(final String proc) {
		UnmodifiableTransFormula oldVarsAssignment = mProc2OldVarsAssignment.get(proc);
		if (oldVarsAssignment == null) {
			oldVarsAssignment = constructOldVarsAssignment(proc);
			mProc2OldVarsAssignment.put(proc, oldVarsAssignment);
		}
		return mProc2OldVarsAssignment.get(proc);
	}
	
	
	/**
	 * Returns a TransFormula that represents an assignment 
	 * g_1,...,g_n :=gOld_1,...,gOld_n
	 * where g_1,...,g_n are the global variables that can be modified by
	 * procedure proc and gOld_1,...,gOld_n are the corresponding oldvars.
	 */
	public UnmodifiableTransFormula getGlobalVarsAssignment(final String proc) {
		UnmodifiableTransFormula globalVarsAssignment = mProc2GlobalVarsAssignment.get(proc);
		if (globalVarsAssignment == null) {
			globalVarsAssignment = constructGlobalVarsAssignment(proc);
			mProc2GlobalVarsAssignment.put(proc, globalVarsAssignment);
		}
		return mProc2GlobalVarsAssignment.get(proc);
	}
	
	

	private UnmodifiableTransFormula constructOldVarsAssignment(final String proc) {
		Set<IProgramNonOldVar> vars = mModifiableGlobalsTable.getModifiedBoogieVars(proc);
		if (vars == null) {
			//no global var modified
			vars = Collections.emptySet();
		}
		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, true, null, true, null, true);
		Term glob2oldFormula = mMgdScript.getScript().term("true");
		for (final IProgramNonOldVar modifiableGlobal : vars) {
			final IProgramOldVar oldVarOfModifiable = modifiableGlobal.getOldVar();
			final Sort sort = modifiableGlobal.getDefaultConstant().getSort();
			
			final String nameIn = modifiableGlobal + "_In";
			final TermVariable tvIn = mMgdScript.getScript().variable(nameIn, sort);
			final String nameOut = "old(" + modifiableGlobal + ")" + "_Out";
			final TermVariable tvOut = mMgdScript.getScript().variable(nameOut, sort);
			tfb.addInVar(modifiableGlobal, tvIn);
			tfb.addOutVar(modifiableGlobal, tvIn);
			tfb.addOutVar(oldVarOfModifiable, tvOut);
			final Term assignment = mMgdScript.getScript().term("=", tvOut, tvIn);
			glob2oldFormula = SmtUtils.and(mMgdScript.getScript(), glob2oldFormula, assignment);
		}
		tfb.setFormula(glob2oldFormula);
		tfb.setInfeasibility(Infeasibility.UNPROVEABLE);
		return tfb.finishConstruction(mMgdScript);
	}


	
	private UnmodifiableTransFormula constructGlobalVarsAssignment(final String proc) {
		Set<IProgramNonOldVar> vars = mModifiableGlobalsTable.getModifiedBoogieVars(proc);
		if (vars == null) {
			//no global var modified
			vars = Collections.emptySet();
		}
		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, true, null, true, null, true);
		Term old2globFormula = mMgdScript.getScript().term("true");
		for (final IProgramNonOldVar modifiableGlobal : vars) {
			final IProgramOldVar oldVarOfModifiable = modifiableGlobal.getOldVar();
			final Sort sort = modifiableGlobal.getDefaultConstant().getSort();
			{
				final String nameIn = "old(" + modifiableGlobal + ")" + "_In";
				final TermVariable tvIn = mMgdScript.getScript().variable(nameIn, sort);
				final String nameOut = modifiableGlobal + "_Out";
				final TermVariable tvOut = mMgdScript.getScript().variable(nameOut, sort);
				tfb.addInVar(oldVarOfModifiable, tvIn);
				tfb.addOutVar(oldVarOfModifiable, tvIn);
				tfb.addOutVar(modifiableGlobal, tvOut);
				final Term assignment = mMgdScript.getScript().term("=", tvOut, tvIn);
				old2globFormula = SmtUtils.and(mMgdScript.getScript(), old2globFormula, assignment);
			}			
		}
		tfb.setFormula(old2globFormula);
		tfb.setInfeasibility(Infeasibility.UNPROVEABLE);
		return tfb.finishConstruction(mMgdScript);
	}
	

}
