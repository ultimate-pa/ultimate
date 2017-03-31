/*
 * Copyright (C) 2017 Jill Enke (enkei@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct;


import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.ListIterator;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctMatrix;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctValue;


/**
 * Parametric Octagons
 * Parametric octagons can (compared to regular octagons)
 * have variables on the right side, so they have the form:
 * +-x+-y <= a*k+b, +-2x <= a*k+b, +-y <= a*k+b 
* @author Jill Enke (enkei@informatik.uni-freiburg.de)
*
*/

public class ParametricOctMatrix {

	private OctMatrix mMatrix;
	private Map<TermVariable, Integer> mVariableMapping;
	private int mSize;

	private boolean mParametric;
	private ParametricOctValue[] mParametricValues;
	private int mMaxValue;
	

	public ParametricOctMatrix() {
		this(0);
	}
	
	public ParametricOctMatrix(int size) {
		mVariableMapping = new HashMap<TermVariable, Integer>();
		mSize = size;
	}

	public int getSize() {
		return mSize;
	}
	
	public void setValue(Object value,
			TermVariable firstVar, boolean firstNegative,
			TermVariable secondVar, boolean secondNegative) {
		int row = -1;
		int column = -1;
		if (mVariableMapping.containsKey(firstVar)) {
			row = mVariableMapping.get(firstVar);
		} else {
			row = addVar(firstVar);
		}
		if (firstVar.equals(secondVar)) {
			column = row;
		} else {
			if (mVariableMapping.containsKey(secondVar)) {
				column = mVariableMapping.get(firstVar);
			} else {
				column = addVar(secondVar);
			}
		}
		
		if (firstNegative) row+=1;
		if (secondNegative) column+=1;
		
		setValue(row, column, (BigDecimal) value);
		
	}
	
	
	private int addVar(TermVariable firstVar) {
		mVariableMapping.put(firstVar, mMaxValue + 2);
		if (mSize < mVariableMapping.size() * 2 + 1) {
			mMatrix = mMatrix.addVariables(1);
			mSize = mVariableMapping.size() * 2 + 1;
			assert mSize == mMatrix.getSize() : "ERROR MATRIX SIZES DO NOT MATCH";
		}
		return 0;
	}
	private void setValue(int row, int col, ParametricOctValue value) {
		
		mParametricValues[getIndex(row, col)] = value;
	}
	
	private void setValue(int row, int column, BigDecimal value) {
		mMatrix.setMin(row, column, new OctValue(value));
	}
	
	private int getIndex(int row, int col) {
		if (row < col) {
			return getLowerIndex(col ^ 1, row ^ 1);
		} else {
			return getLowerIndex(row, col);
		}
	}

	private int getLowerIndex(int row, int col) {
		return col + (row + 1) * (row + 1) / 2;
	}
	
	public ParametricOctMatrix multiplyVar(String varname, Script script) {
		TermVariable var = script.variable(varname, script.sort("Int"));
		return this.multipyVar(var);
		
	}
	
	public ParametricOctMatrix multipyVar(TermVariable var) {

		return null;
	}

	
}
