/*
 * Copyright (C) 2017 Ben Biesenbach (ben.biesenbach@gmx.de)
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Matrix to store vectors for {@link LoopAccelerationMatrix}
 * 
 * @author Ben Biesenbach (Ben.Biesenbach@gmx.de)
 */
public class MatrixBB {
	
	private Map<Integer, Map<Term, Term>> mMatrix = new HashMap<>();
	private Map<Integer, Map<Term, Term>> mLGS = new HashMap<>();
	private Map<IProgramVar, TermVariable> mInVars;
	private ILogger mLogger;
	
	/**
	 * Matrix to store vectors for {@link LoopAccelerationMatrix}
	 * 
	 * @param inVars
	 * @param logger
	 */
	public MatrixBB(Map<IProgramVar, TermVariable> inVars, ILogger logger){
		mLogger = logger;
		mInVars = inVars;
	}
	
	public void print(){
		mMatrix.entrySet().forEach(vector 
				-> mLogger.info("#" + vector.getKey() + ": " + vector.getValue() + " -> " + mLGS.get(vector.getKey())));
	}
	
	public void setVector(Map<Term,Term> vector, int index){
		mMatrix.put(index, vector);
	}
	
	public void setSolution(Map<Term,Term> vectorSolution, int index){
		mLGS.put(index, vectorSolution);
	}
	
	public Map<Integer, Map<Term, Term>> getLGS(){
		return mLGS;
	}
	
	public Map<Integer, Map<Term, Term>> getMatrix(){
		return mMatrix;
	}
}