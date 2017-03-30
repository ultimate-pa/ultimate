package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class MatrixBB {
	
	private int[][] mMatrixInt;
	private Term[][] mMatrixTerm;
	private int mMatrixSize;
	private int mNumberOfVariables;
	private ILogger mLogger;
	
	public MatrixBB(int numberOfVariables, ILogger logger){
		mLogger = logger;
		mNumberOfVariables = numberOfVariables;
		mMatrixSize = numberOfVariables * 2 + 2;
		mMatrixInt = new int[mMatrixSize][mMatrixSize];
		mMatrixTerm = new Term[numberOfVariables+1][numberOfVariables];
		
		init(numberOfVariables);
	}
	
	private void init(int numberOfVariables){
		//n(matrix) = 0
		for(int i = 0; i < numberOfVariables; i++){
			mMatrixInt[i][i] = 1;
		}
	}
	
	public void setVector(int vectorNumber, int[] values, Term[] term, int n){
		for(int i = 0; i < mNumberOfVariables; i++){
			mMatrixInt[vectorNumber][i] = values[i];
			mMatrixInt[vectorNumber][i + mNumberOfVariables + 1] = values[i];
		}
		mMatrixInt[vectorNumber][mNumberOfVariables] = n;
		mMatrixInt[vectorNumber][mMatrixSize-1] = n * n;
		setVectorTerm(vectorNumber, term);
	}
	
	/**
	 * Prints the matrix in the logger
	 */
	public void print(){
		for(int i = 0; i < mMatrixInt.length; i++){
			String line = "";
			for(int j = 0; j < mMatrixInt.length; j++){
				line += Integer.toString(mMatrixInt[i][j]);
			}
			mLogger.info(line);
		}
	}
	
	public int[] getVectorInt(int vectorNumber){
		return mMatrixInt[vectorNumber];
	}
	
	private void setVectorTerm(int vectorNumber, Term[] term){
		mMatrixTerm[vectorNumber - mNumberOfVariables] = term;
	}
	
	public Term[] getVectorTerm(int vectorNumber){
		return mMatrixTerm[vectorNumber-mNumberOfVariables];
	}
	
	public int[] getResult(){
		//TODO calculate alphas
		return null;
	}
}
