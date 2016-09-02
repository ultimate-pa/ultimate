/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

public class BuchiModGlobalVarManager extends ModifiableGlobalVariableManager {
	private final IProgramNonOldVar mUnseeded;
	private final IProgramNonOldVar[] mOldRank;
	private final IProgramOldVar mUnseededOldVar;
	private final IProgramOldVar[] mOldRankOldVar;
	
	private final Map<String, UnmodifiableTransFormula> mProc2OldVarsAssignment;
	private final Map<String, UnmodifiableTransFormula> mProc2GlobalVarsAssignment;

	public BuchiModGlobalVarManager(final IProgramNonOldVar unseeded, final IProgramNonOldVar[] oldRank,
			final ModifiableGlobalVariableManager modifiableGlobalVariableManager, 
			final Boogie2SMT boogie2Smt) {
		super(modifiableGlobalVariableManager);
		mUnseeded = unseeded;
		mUnseededOldVar = unseeded.getOldVar();
		assert mUnseededOldVar != null : "oldVar missing";
		mOldRank = oldRank;
		mOldRankOldVar = new IProgramOldVar[oldRank.length];
		for (int i=0; i<oldRank.length; i++) {
			mOldRankOldVar[i] = oldRank[i].getOldVar();
			assert mOldRankOldVar[i] != null : "oldVar missing";
		}
		mProc2OldVarsAssignment = new HashMap<String, UnmodifiableTransFormula>();
		mProc2GlobalVarsAssignment = new HashMap<String, UnmodifiableTransFormula>();
	}

	
	@Override
	public UnmodifiableTransFormula getOldVarsAssignment(final String proc) {
		UnmodifiableTransFormula oldVarsAssignment = mProc2OldVarsAssignment.get(proc);
		if (oldVarsAssignment == null) {
			oldVarsAssignment = constructOldVarsAssignment(proc);
			mProc2OldVarsAssignment.put(proc, oldVarsAssignment);
		}
		return mProc2OldVarsAssignment.get(proc);
	}
	
	

	@Override
	public UnmodifiableTransFormula getGlobalVarsAssignment(final String proc) {
		UnmodifiableTransFormula globalVarsAssignment = mProc2GlobalVarsAssignment.get(proc);
		if (globalVarsAssignment == null) {
			globalVarsAssignment = constructGlobalVarsAssignment(proc);
			mProc2GlobalVarsAssignment.put(proc, globalVarsAssignment);
		}
		return mProc2GlobalVarsAssignment.get(proc);
	}
	
	
	private UnmodifiableTransFormula constructOldVarsAssignment(final String proc) {
		final UnmodifiableTransFormula without = super.getOldVarsAssignment(proc);
		assert without.getAuxVars().isEmpty();
		assert without.getBranchEncoders().isEmpty();
		assert without.isInfeasible() == Infeasibility.UNPROVEABLE;
		
		final TransFormulaBuilder tfb = new TransFormulaBuilder(
				without.getInVars(), without.getOutVars(), true, null, true);
		Term formula = without.getFormula();
		formula = Util.and(mMgdScript.getScript(), formula, oldVarEquality(mUnseeded, mUnseededOldVar));
		tfb.addInVar(mUnseeded, mUnseeded.getTermVariable());
		tfb.addOutVar(mUnseeded, mUnseeded.getTermVariable());
		tfb.addOutVar(mUnseededOldVar, mUnseededOldVar.getTermVariable());
		for (int i=0; i<mOldRank.length; i++) {
			formula = Util.and(mMgdScript.getScript(), formula, oldVarEquality(mOldRank[i], mOldRankOldVar[i]));
			tfb.addInVar(mOldRank[i], mOldRank[i].getTermVariable());
			tfb.addOutVar(mOldRank[i], mOldRank[i].getTermVariable());
			tfb.addOutVar(mOldRankOldVar[i], mOldRankOldVar[i].getTermVariable());
		}
		tfb.setFormula(formula);
		tfb.setInfeasibility(Infeasibility.UNPROVEABLE);
		return tfb.finishConstruction(mMgdScript);
	}
	
	
	private UnmodifiableTransFormula constructGlobalVarsAssignment(final String proc) {
		final UnmodifiableTransFormula without = super.getGlobalVarsAssignment(proc);
		assert without.getAuxVars().isEmpty();
		assert without.getBranchEncoders().isEmpty();
		assert without.isInfeasible() == Infeasibility.UNPROVEABLE;
		
		final TransFormulaBuilder tfb = new TransFormulaBuilder(
				without.getInVars(), without.getOutVars(), true, null, true);
		Term formula = without.getFormula();
		formula = Util.and(mMgdScript.getScript(), formula, oldVarEquality(mUnseeded, mUnseededOldVar));
		tfb.addInVar(mUnseededOldVar, mUnseededOldVar.getTermVariable());
		tfb.addOutVar(mUnseededOldVar, mUnseededOldVar.getTermVariable());
		tfb.addOutVar(mUnseeded, mUnseeded.getTermVariable());
		for (int i=0; i<mOldRank.length; i++) {
			formula = Util.and(mMgdScript.getScript(), formula, oldVarEquality(mOldRank[i], mOldRankOldVar[i]));
			tfb.addInVar(mOldRankOldVar[i], mOldRankOldVar[i].getTermVariable());
			tfb.addOutVar(mOldRankOldVar[i], mOldRankOldVar[i].getTermVariable());
			tfb.addOutVar(mOldRank[i], mOldRank[i].getTermVariable());
		}
		tfb.setFormula(formula);
		tfb.setInfeasibility(Infeasibility.UNPROVEABLE);
		return tfb.finishConstruction(mMgdScript);
	}


	
	public Term oldVarEquality(final IProgramVar var, final IProgramVar oldVar) {
		return mMgdScript.getScript().term("=", var.getTermVariable(), oldVar.getTermVariable());
	}


	@Override
	public Map<String, IProgramNonOldVar> getGlobals() {
		final HashMap<String, IProgramNonOldVar> result = 
				new HashMap<String, IProgramNonOldVar>(super.getGlobals());
		for (int i=0; i<mOldRank.length; i++) {
			result.put(mOldRank[i].getIdentifier(),mOldRank[i]);
		}
		result.put(mUnseeded.getIdentifier(),mUnseeded);
		return result;
	}

}
