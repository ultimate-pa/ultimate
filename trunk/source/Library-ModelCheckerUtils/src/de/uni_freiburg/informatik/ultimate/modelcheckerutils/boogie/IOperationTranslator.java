/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;

/**
 * @author thomas
 *
 */
public interface IOperationTranslator {

	public String opTranslation(BinaryExpression.Operator op, IType type1, IType type2);
	public String opTranslation(UnaryExpression.Operator op, IType type);
}
