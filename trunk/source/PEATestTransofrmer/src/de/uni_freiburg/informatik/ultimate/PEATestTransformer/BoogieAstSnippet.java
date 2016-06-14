package de.uni_freiburg.informatik.ultimate.PEATestTransformer;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;

public class BoogieAstSnippet {
	
	/** Creates dummy location in file "Test" line 0
	 * @return
	 */
	public static ILocation createDummyLocation(){
		return createDummyLocation("TEST");
	}
	public static ILocation createDummyLocation(String fileName){
		return new BoogieLocation(fileName,0,0,0,0,false);
	}
	
	/** Creates an identifier expression with a dummy location
	 * @param ident
	 * @return
	 */
	public static IdentifierExpression createIdentifier(String ident, ILocation location){
		return new IdentifierExpression(
				location,ident);
	}
	public static IdentifierExpression createIdentifier(String ident, String fileName){
		return new IdentifierExpression(
				createDummyLocation(fileName),ident);
	}
	public static IdentifierExpression createIdentifier(String ident){
		return createIdentifier(ident, "TEST");
	}
	
	/**
	 * Creates dummy binary comparision expression.
	 * @param a
	 * @param b
	 * @return
	 */
	public static Expression createBooleanExpression(String a, Expression e, BinaryExpression.Operator op){
		return new BinaryExpression(createDummyLocation(), op, 
				createIdentifier(a), e);
	}
	public static Expression createBooleanExpression(String a, String b, BinaryExpression.Operator op){
		return new BinaryExpression(createDummyLocation(), op, 
				createIdentifier(a), createIdentifier(b));
	}
	public static Expression createBooleanExpression(String a, String b){
		return createBooleanExpression(a,b, BinaryExpression.Operator.COMPEQ);
	}
	
	public static Expression createConjunction(Expression[] conjuncts){
		if (conjuncts.length == 1) return conjuncts[0];
		Expression result = new BinaryExpression(createDummyLocation(), BinaryExpression.Operator.LOGICAND,
				conjuncts[0], conjuncts[1]);
		for(int i = 2; i < conjuncts.length; i++){
			result = new BinaryExpression(createDummyLocation(), BinaryExpression.Operator.LOGICAND,
					result, conjuncts[i]);
		}
		return result;
	}

}
