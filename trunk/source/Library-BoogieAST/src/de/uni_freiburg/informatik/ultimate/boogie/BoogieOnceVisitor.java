package de.uni_freiburg.informatik.ultimate.boogie;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;

/**
 * Like {@link BoogieVisitor}, but visits each Expression only once.
 *
 * Implementation note: We catch the visit calls before they are done by super.process..
 * That way we don't need to use Caching BoogieVisitor either.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class BoogieOnceVisitor extends BoogieVisitor {

	Map<BoogieASTNode, BoogieASTNode> mCache = new HashMap<>();

	@Override
	protected Declaration processDeclaration(final Declaration decl) {
		BoogieASTNode result = mCache.get(decl);
		if (result == null) {
			result = super.processDeclaration(decl);
			mCache.put(decl, result);
		}
		return (Declaration) result;
	}

	@Override
	protected ASTType processType(final ASTType type) {
		BoogieASTNode result = mCache.get(type);
		if (result == null) {
		result = super.processType(type);
		mCache.put(type, result);
	}
	return (ASTType) result;

	}

	@Override
	protected Statement processStatement(final Statement statement) {
		BoogieASTNode result = mCache.get(statement);
		if (result == null) {
		result = super.processStatement(statement);
		mCache.put(statement, result);
	}
	return statement;

	}

	@Override
	protected LeftHandSide processLeftHandSide(final LeftHandSide lhs) {
		BoogieASTNode result = mCache.get(lhs);
		if (result == null) {
			result = super.processLeftHandSide(lhs);
			mCache.put(lhs, result);
		}
		return (LeftHandSide) result;
	}

	@Override
	protected Specification processSpecification(final Specification spec) {
		BoogieASTNode result = mCache.get(spec);
		if (result == null) {
		result = super.processSpecification(spec);
		mCache.put(spec, result);
	}
	return (Specification) result;

	}

	@Override
	protected Attribute processAttribute(final Attribute attr) {
		BoogieASTNode result = mCache.get(attr);
		if (result == null) {
			result = super.processAttribute(attr);
			mCache.put(attr, result);
		}
		return (Attribute) result;
	}

	@Override
	protected Expression processExpression(final Expression expr) {
		BoogieASTNode result = mCache.get(expr);
		if (result == null) {
			result = super.processExpression(expr);
			mCache.put(expr, result);
		}
		return (Expression) result;
	}





}
