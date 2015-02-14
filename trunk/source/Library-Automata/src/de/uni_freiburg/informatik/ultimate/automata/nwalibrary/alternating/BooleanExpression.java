package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating;

import java.util.List;

public class BooleanExpression{

	public BooleanExpression(long alpha, long beta){
		this.alpha = alpha;
		this.beta = beta;
	}
	private long alpha;
	private long beta;
	private BooleanExpression nextConjunctExpression;
	
	public void addConjunction(BooleanExpression booleanExpression){
		if(nextConjunctExpression != null){
			nextConjunctExpression.addConjunction(booleanExpression);
		}
		else{
			nextConjunctExpression = booleanExpression;
		}
	}
	
	public boolean getResult(long bitVector){
		long result = ((bitVector & alpha) ^ beta);
		if(result == 0){
			return true;
		}
		else if(nextConjunctExpression != null){
			return nextConjunctExpression.getResult(bitVector);
		}
		return false;
	}
	
	public BooleanExpression cloneShifted(int amount){
		BooleanExpression booleanExpression = new BooleanExpression(alpha << amount, beta << amount);
		if(nextConjunctExpression != null){
			booleanExpression.nextConjunctExpression = nextConjunctExpression.cloneShifted(amount);
		}
		return booleanExpression;
	}
	
	public <T> String toString(List<T> variables){
		String text = "";
		int r = 0;
		for(int i=0;i<variables.size();i++){
			if(BitUtil.getBit(alpha, i)){
				if(r != 0){
					text += " ^ ";
				}
				if(!BitUtil.getBit(beta, i)){
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
}
