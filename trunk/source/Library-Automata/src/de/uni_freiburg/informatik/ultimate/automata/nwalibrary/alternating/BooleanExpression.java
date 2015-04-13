package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating;

import java.util.BitSet;
import java.util.List;

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
	
	public BooleanExpression cloneShifted(int amount){
		BitSet shiftedAlpha = new BitSet(alpha.size() + amount);
		BitSet shiftedBeta = new BitSet(beta.size() + amount);
		for(int i=0;i<alpha.size();i++){
			shiftedAlpha.set(i + amount, alpha.get(i));
			shiftedBeta.set(i + amount, beta.get(i));
		}
		BooleanExpression booleanExpression = new BooleanExpression(shiftedAlpha, shiftedBeta);
		if(nextConjunctExpression != null){
			booleanExpression.nextConjunctExpression = nextConjunctExpression.cloneShifted(amount);
		}
		return booleanExpression;
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
