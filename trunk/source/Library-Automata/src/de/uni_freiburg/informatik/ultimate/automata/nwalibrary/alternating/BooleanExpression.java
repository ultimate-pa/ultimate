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
