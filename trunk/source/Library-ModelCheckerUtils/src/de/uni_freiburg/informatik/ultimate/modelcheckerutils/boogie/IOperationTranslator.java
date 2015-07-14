package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;

/**
 * @author Thomas Lang
 *
 */
public interface IOperationTranslator {

	public String opTranslation(BinaryExpression.Operator op, IType type1, IType type2);
	public String opTranslation(UnaryExpression.Operator op, IType type);
	
	public String funcApplication(String funcIdentifier, IType[] argumentTypes);
	
	public Term booleanTranslation(BooleanLiteral exp);
	public Term bitvecTranslation(BitvecLiteral exp);
	public Term integerTranslation(IntegerLiteral exp);
	public Term realTranslation(RealLiteral exp);
}
