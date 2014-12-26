package de.uni_freiburg.informatik.ultimate.model.boogie;

import de.uni_freiburg.informatik.ultimate.model.ModelUtils;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WildcardExpression;
/**
 * Construct deep copy of an Boogie AST.
 * @author Matthias Heizmann
 *
 */
public class BoogieAstCopier extends BoogieTransformer {
	
	public Unit copy(Unit unit) {
		Declaration[] oldDeclarations = unit.getDeclarations();
		Declaration[] newDeclarations = new Declaration[oldDeclarations.length];
		for (int i=0; i<oldDeclarations.length; i++) {
			newDeclarations[i] = processDeclaration(oldDeclarations[i]);
		}
		return new Unit(unit.getLocation(), newDeclarations);
	}

	@Override
	protected Expression processExpression(Expression expr) {
		final Expression result;
		if (expr instanceof IdentifierExpression) {
			IdentifierExpression idExpr = (IdentifierExpression) expr;
			IdentifierExpression resultIdExpr = new IdentifierExpression(idExpr.getLocation(), idExpr.getIdentifier());
			resultIdExpr.setDeclarationInformation(idExpr.getDeclarationInformation());
			result = resultIdExpr;
			ModelUtils.mergeAnnotations(expr, result);
		}
		else if (expr instanceof BooleanLiteral) {
			BooleanLiteral boolLit = (BooleanLiteral) expr;
			result = new BooleanLiteral(boolLit.getLocation(), boolLit.getType(), boolLit.getValue());
			ModelUtils.mergeAnnotations(expr, result);
		} else if (expr instanceof IntegerLiteral) {
			IntegerLiteral intLit = (IntegerLiteral) expr;
			result = new IntegerLiteral(intLit.getLocation(), intLit.getType(), intLit.getValue());
			ModelUtils.mergeAnnotations(expr, result);
		} else if (expr instanceof BitvecLiteral) {
			BitvecLiteral bitvecLit = (BitvecLiteral) expr;
			result = new BitvecLiteral(bitvecLit.getLocation(), bitvecLit.getType(), bitvecLit.getValue(), bitvecLit.getLength());
			ModelUtils.mergeAnnotations(expr, result);
		} else if (expr instanceof StringLiteral) {
			StringLiteral stringLit = (StringLiteral) expr;
			result = new StringLiteral(stringLit.getLocation(), stringLit.getType(), stringLit.getValue());
			ModelUtils.mergeAnnotations(expr, result);
		} else if (expr instanceof WildcardExpression) {
			result = new WildcardExpression(expr.getLocation(), expr.getType());
			ModelUtils.mergeAnnotations(expr, result);
		} else {
			result = super.processExpression(expr);
		}
		return result;
	}
	
	
}
