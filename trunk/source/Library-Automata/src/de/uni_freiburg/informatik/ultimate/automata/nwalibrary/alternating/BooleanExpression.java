/*
 * Copyright (C) 2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Carl Kuesters
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating;

import java.util.BitSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

public class BooleanExpression{

	public BooleanExpression(BitSet alpha, BitSet beta){
		this.alpha = alpha;
		this.beta = beta;
	}
	private BitSet alpha;
	private BitSet beta;
	private BooleanExpression nextConjunctExpression;
	
	public void addConjunction(BooleanExpression booleanExpression){
		if(!containsConjunction(booleanExpression)){
			if(nextConjunctExpression != null){
				nextConjunctExpression.addConjunction(booleanExpression);
			}
			else{
				nextConjunctExpression = booleanExpression;
			}
		}
	}
	
	public boolean containsConjunction(BooleanExpression booleanExpression){
		if(equals(booleanExpression)){
			return true;
		}
		else if(nextConjunctExpression != null){
			nextConjunctExpression.containsConjunction(booleanExpression);
		}
		return false;
	}
	
	public boolean getResult(BitSet bitVector){
		BitSet result = (BitSet) bitVector.clone();
		result.and(alpha);
		result.xor(beta);
		if(result.isEmpty()){
			return true;
		}
		else if(nextConjunctExpression != null){
			return nextConjunctExpression.getResult(bitVector);
		}
		return false;
	}
	
	public BooleanExpression cloneShifted(Map<Integer,Integer> shiftMap, int newSize){
		BitSet shiftedAlpha = new BitSet(newSize);
		BitSet shiftedBeta = new BitSet(newSize);
		for (Entry<Integer, Integer> entry : shiftMap.entrySet()) {
			if (alpha.get(entry.getKey()))
				shiftedAlpha.set(entry.getValue());
			if (beta.get(entry.getKey()))
				shiftedBeta.set(entry.getValue());
		}	
		BooleanExpression result = new BooleanExpression(shiftedAlpha, shiftedBeta);
		if(nextConjunctExpression != null){
			result.nextConjunctExpression = nextConjunctExpression.cloneShifted(shiftMap, newSize);
		}	
		return result;
	}
	
	public boolean equals(BooleanExpression booleanExpression){
		return (alpha.equals(booleanExpression.alpha) && beta.equals(booleanExpression.beta));
	}
	
	public <T> String toString(List<T> variables){
		String text = "";
		int r = 0;
		for(int i=0;i<variables.size();i++){
			if(alpha.get(i)){
				if(r != 0){
					text += " ^ ";
				}
				if(!beta.get(i)){
					text += "~";
				}
				text += variables.get(i);
				r++;
			}
		}
		if(nextConjunctExpression != null){
			if(r > 1){
				text = "(" + text + ")";
			}
			text += " v " + nextConjunctExpression.toString(variables);
		}
		return text;
	}
	
	public BitSet getAlpha() {
		return alpha;
	}
	
	public BitSet getBeta() {
		return beta;
	}
	
	public BooleanExpression getNextConjunctExpression() {
		return nextConjunctExpression;
	}
}
