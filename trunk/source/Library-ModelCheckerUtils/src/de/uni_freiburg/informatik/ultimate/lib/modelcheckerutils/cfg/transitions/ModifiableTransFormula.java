/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SMTPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;


/**
 * {@link TransFormula} that can be modified. Stores additionally a
 * mapping from {@link TermVariable}s to {@link IProgramVar}s. 
 * 
 * @author Jan Leike
 * @author Matthias Heizmann
 * 
 * @see VarFactory
 * @see IProgramVar
 */
public class ModifiableTransFormula extends TransFormula {
	
	private final Map<TermVariable, IProgramVar> mInVarsReverseMapping;
	private final Map<TermVariable, IProgramVar> mOutVarsReverseMapping;
	
	private Term mFormula;
	
	/**
	 * Create a new TransformulaLR
	 * @param formula the transition formula
	 */
	public ModifiableTransFormula(final Term formula) {
		super(new LinkedHashMap<>(), new LinkedHashMap<>(), new LinkedHashSet<>(), new LinkedHashSet<>());
		mInVarsReverseMapping = new LinkedHashMap<>();
		mOutVarsReverseMapping = new LinkedHashMap<>();
		mFormula = formula;
	}
	
	/**
	 * Copy constructor
	 */
	public ModifiableTransFormula(final ModifiableTransFormula other) {
		this(other.getFormula());
		mInVars.putAll(other.mInVars);
		mInVarsReverseMapping.putAll(other.mInVarsReverseMapping);
		mOutVars.putAll(other.mOutVars);
		mOutVarsReverseMapping.putAll(other.mOutVarsReverseMapping);
		mAuxVars.addAll(other.mAuxVars);
		mNonTheoryConsts.addAll(other.mNonTheoryConsts);
	}
	
	
	
	/**
	 * @return mapping from inVars to the RankVar that is represented by the
	 * inVar
	 */
	public Map<Term, IProgramVar> getInVarsReverseMapping() {
		return Collections.unmodifiableMap(mInVarsReverseMapping);
	}

	/**
	 * @return mapping from outVars to the RankVar that is represented by the
	 * outVar
	 */
	public Map<Term, IProgramVar> getOutVarsReverseMapping() {
		return Collections.unmodifiableMap(mOutVarsReverseMapping);
	}
	
	/**
	 * Add an inVar to the collection
	 * @param rkVar a RankVar
	 * @param var the TermVariable corresponding to the RankVar's input state
	 *            (unprimed version)
	 */
	public void addInVar(final IProgramVar rkVar, final TermVariable var) {
		final Term oldValue = mInVars.put(rkVar, var);
		if (oldValue == null) {
			mInVarsReverseMapping.put(var, rkVar);
		} else {
			if (oldValue != var) {
				throw new IllegalArgumentException(
						oldValue + " is already the inVar of " + rkVar);
			}
		}
	}
	
	/**
	 * Remove an inVar from the collection
	 */
	public void removeInVar(final IProgramVar rkVar) {
		final Term tv = mInVars.remove(rkVar);
		if (tv == null) {
			throw new AssertionError(
					"cannot remove variable that is not contained");
		} else {
			mInVarsReverseMapping.remove(tv);
		}
	}
	
	/**
	 * Add an outVar to the collection
	 * @param rkVar a RankVar
	 * @param var the TermVariable corresponding to the RankVar's output state
	 *            (primed version)
	 */
	public void addOutVar(final IProgramVar rkVar, final TermVariable var) {
		final Term oldValue = mOutVars.put(rkVar, var);
		if (oldValue == null) {
			mOutVarsReverseMapping.put(var, rkVar);
		} else {
			if (oldValue != var) {
				throw new IllegalArgumentException(
						oldValue + " is already the outVar of " + rkVar);
			}
		}
	}
	
	/**
	 * Remove an outVar from the collection
	 */
	public void removeOutVar(final IProgramVar rkVar) {
		final Term tv = mOutVars.remove(rkVar);
		if (tv == null) {
			throw new AssertionError(
					"cannot remove variable that is not contained");
		} else {
			mOutVarsReverseMapping.remove(tv);
		}
	}
	
	public void removeAuxVar(final TermVariable auxVar) {
		final boolean modified = mAuxVars.remove(auxVar);
		if (!modified) {
			throw new AssertionError(
					"cannot remove variable that is not contained");
		}
	}
	
	
	/**
	 * Add a TermVariables that each neither occur as inVar or outVar to the set
	 * of auxiliary variables. (Note that auxiliary variables are different from
	 * replacement variables).
	 */
	public void addAuxVars(final Set<TermVariable> auxVars) {
		mAuxVars.addAll(auxVars);
	}
	
	/**
	 * @return the transition formula
	 */
	@Override
	public Term getFormula() {
		return mFormula;
	}
	
	/**
	 * @param term the new transition formula
	 */
	public void setFormula(final Term formula) {
		mFormula = formula;
	}
	
	/**
	 * Returns true if each auxVar occurs neither as inVar nor as outVar.
	 * This property should always hold.
	 */
	public boolean auxVarsDisjointFromInOutVars() {
		for (final Term auxVar : mAuxVars) {
			if (mInVarsReverseMapping.containsKey(auxVar)) {
				return false;
			}
			if (mOutVarsReverseMapping.containsKey(auxVar)) {
				return false;
			}
		}
		return true;
	}
	
	/**
	 * Returns some TermVariable from tvs that occurs neither as inVar nor
	 * as outVar nor as auxVar. Returns null if no such TermVariable in tvs
	 * exists.
	 * For the variables that occur in the transition that uses this
	 * VarCollector the result should always be null.
	 */
	public TermVariable allAreInOutAux(final TermVariable[] tvs) {
		for (final TermVariable tv : tvs) {
			if (!isInOurAux(tv)) {
				return tv;
			}
		}
		return null;
	}
	
	/**
	 * @return the set of assigned/updated variables. A variable is updated by
	 * this transition if it occurs as outVar and
     * - it does not occur as inVar
	 * - or the inVar is represented by a different TermVariable
	 */
	@Override
	public Set<IProgramVar> getAssignedVars() {
		return Collections.unmodifiableSet(TransFormulaUtils.computeAssignedVars(mInVars, mOutVars));
	}
	
	/**
	 * @return whether the TermVariable tv occurs as inVar, outVar, or auxVar.
	 */
	private boolean isInOurAux(final TermVariable tv) {
		if (mInVarsReverseMapping.containsKey(tv) || mOutVarsReverseMapping.containsKey(tv)) {
			return true;
		}
		return mAuxVars.contains(tv);
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("InVars: ");
		sb.append(mInVars.toString());
		sb.append("\nOutVars: ");
		sb.append(mOutVars.toString());
		sb.append("\nAuxVars: ");
		sb.append(mAuxVars.toString());
		sb.append("\nTransition formula: ");
		sb.append(new SMTPrettyPrinter(mFormula));
		return sb.toString();
	}
}
