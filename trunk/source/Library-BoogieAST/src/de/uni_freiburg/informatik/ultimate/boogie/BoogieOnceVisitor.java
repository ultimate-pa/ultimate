/*
 * Copyright (C) 2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
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
 * Implementation note: We catch the visit calls before they are done by super.process.. That way we don't need to use
 * Caching BoogieVisitor either.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class BoogieOnceVisitor extends BoogieVisitor {

	private final Map<BoogieASTNode, BoogieASTNode> mCache = new HashMap<>();

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
	protected <T extends Attribute> T processAttribute(final T attr) {
		BoogieASTNode result = mCache.get(attr);
		if (result == null) {
			result = super.processAttribute(attr);
			mCache.put(attr, result);
		}
		return (T) result;
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
