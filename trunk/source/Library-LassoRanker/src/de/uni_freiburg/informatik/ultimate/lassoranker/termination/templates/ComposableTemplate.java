/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE LassoRanker Library.
 * 
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.termination.templates;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Superclass for ranking templates that can be composed into larger templates
 * by the combosed template.
 * 
 * @author Jan Leike
 */
public abstract class ComposableTemplate extends RankingTemplate {
	/**
	 * Generate the constraints in form of linear inequalities in CNF
	 * that the ranking function decreases
	 * 
	 * Must be initialized before calling this!
	 * 
	 * @param inVars  Input variables for the loop transition
	 * @param outVars Output variables for the loop transition
	 */
	public abstract List<List<LinearInequality>> getConstraintsDec(
			Map<IProgramVar, TermVariable> inVars, Map<IProgramVar, TermVariable> outVars);
	
	/**
	 * Generate the constraints in form of linear inequalities in CNF
	 * that the ranking function does not increase
	 * 
	 * Must be initialized before calling this!
	 * 
	 * @param inVars  Input variables for the loop transition
	 * @param outVars Output variables for the loop transition
	 */
	public abstract List<List<LinearInequality>> getConstraintsNonInc(
			Map<IProgramVar, TermVariable> inVars, Map<IProgramVar, TermVariable> outVars);
	
	/**
	 * Generate the constraints in form of linear inequalities in CNF
	 * that the ranking function is bounded from below
	 * 
	 * Must be initialized before calling this!
	 * 
	 * @param inVars  Input variables for the loop transition
	 * @param outVars Output variables for the loop transition
	 */
	public abstract List<List<LinearInequality>> getConstraintsBounded(
			Map<IProgramVar, TermVariable> inVars, Map<IProgramVar, TermVariable> outVars);
	
	/**
	 * @return the annotations for getConstraintsDec()
	 */
	public abstract List<String> getAnnotationsDec();
	
	/**
	 * @return the annotations for getConstraintsNonInc()
	 */
	public abstract List<String> getAnnotationsNonInc();
	
	/**
	 * @return the annotations for getConstraintsBounded()
	 */
	public abstract List<String> getAnnotationsBounded();
	
	@Override
	public List<List<LinearInequality>> getConstraints(
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars) {
		checkInitialized();
		// The ranking function decreases and is bounded from below
		final List<List<LinearInequality>> constraints
			= new ArrayList<List<LinearInequality>>();
		constraints.addAll(getConstraintsDec(inVars, outVars));
		constraints.addAll(getConstraintsBounded(inVars, outVars));
		return constraints;
	}
	
	@Override
	public List<String> getAnnotations() {
		checkInitialized();
		final List<String> annotations = new ArrayList<String>();
		annotations.addAll(getAnnotationsDec());
		annotations.addAll(getAnnotationsBounded());
		return annotations;
	}
}
