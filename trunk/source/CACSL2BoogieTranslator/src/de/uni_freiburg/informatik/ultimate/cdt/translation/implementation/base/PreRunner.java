/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTFieldReference;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTSimpleDeclaration;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.LinkedScopedHashMap;

/**
 * @authors Markus Lindenmann, Alexander Nutz
 * @date 12.12.2012
 */
public class PreRunner extends ASTVisitor {
	/**
	 * The table containing all functions.
	 */
	private final Map<String, IASTNode> mFunctionTable;
	/**
	 * The symbol table during the translation.
	 */
	private final LinkedScopedHashMap<String, IASTNode> mTemporarySymbolTable;
	/**
	 * The symbol table used for renaming IDs according to multiparse rules.
	 */
	private final FlatSymbolTable mSymTab;

	/**
	 * Every function that is pointed to
	 */
	private final LinkedHashSet<String> mFunctions;

	/**
	 * Constructor.
	 */
	public PreRunner(final FlatSymbolTable symTab, final Map<String, IASTNode> functionTable) {
		shouldVisitDeclarations = true;
		shouldVisitParameterDeclarations = true;
		shouldVisitExpressions = true;
		shouldVisitStatements = true;
		shouldVisitDeclSpecifiers = true;
		mSymTab = symTab;
		mTemporarySymbolTable = new LinkedScopedHashMap<>();
		mFunctionTable = functionTable;
		mFunctions = new LinkedHashSet<>();
	}

	public Set<String> getResult() {
		return Collections.unmodifiableSet(mFunctions);
	}

	@Override
	public int visit(final IASTDeclSpecifier declSpec) {
		if (declSpec instanceof IASTCompositeTypeSpecifier) {
			mTemporarySymbolTable.beginScope();
		}
		return super.visit(declSpec);
	}

	@Override
	public int leave(final IASTDeclSpecifier declSpec) {
		if (declSpec instanceof IASTCompositeTypeSpecifier) {
			mTemporarySymbolTable.endScope();
		}
		return super.leave(declSpec);
	}

	@Override
	public int visit(final IASTParameterDeclaration declaration) {
		String name = declaration.getDeclarator().getName().toString();
		if (name.isEmpty() && declaration.getDeclarator() instanceof IASTFunctionDeclarator) {
			name = declaration.getDeclarator().getNestedDeclarator().getName().toString();
		}

		mTemporarySymbolTable.put(name, declaration);
		return super.visit(declaration);
	}

	@Override
	public int visit(final IASTExpression expression) {
		if (expression instanceof IASTUnaryExpression) {
			final IASTUnaryExpression ue = (IASTUnaryExpression) expression;
			if (ue.getOperator() == IASTUnaryExpression.op_amper) {
				final String id = extractExpressionId(ue.getOperand());
				if (id != null) {
					addFunction(id, expression.getContainingFilename());
				}
			}
		} else if (expression instanceof IASTIdExpression
				&& !(expression.getParent() instanceof IASTFunctionCallExpression
						&& ((IASTFunctionCallExpression) expression.getParent()).getFunctionNameExpression()
								.equals(expression))) {
			// a function address may be assigned to a function pointer without addressof
			// like fptr = f; where f is a function
			final String id = ((IASTIdExpression) expression).getName().toString();
			addFunction(id, expression.getContainingFilename());
		}
		return super.visit(expression);
	}

	@Override
	public int visit(final IASTDeclaration declaration) {
		if (declaration instanceof CASTSimpleDeclaration) {
			final CASTSimpleDeclaration cd = (CASTSimpleDeclaration) declaration;
			for (final IASTDeclarator d : cd.getDeclarators()) {
				for (IASTDeclarator nd = d; nd != null; nd = nd.getNestedDeclarator()) {
					addNameOfNonFunctionDeclarator(nd);
				}
			}

		} else if (declaration instanceof IASTFunctionDefinition) {
			mTemporarySymbolTable.beginScope();
		}
		return super.visit(declaration);
	}

	@Override
	public int leave(final IASTDeclaration declaration) {
		if (declaration instanceof IASTFunctionDefinition) {
			mTemporarySymbolTable.endScope();
		}
		return super.visit(declaration);
	}

	@Override
	public int visit(final IASTStatement statement) {
		if (statement instanceof IASTCompoundStatement && !(statement.getParent() instanceof IASTFunctionDefinition
				|| statement.getParent() instanceof IASTForStatement)) {
			mTemporarySymbolTable.beginScope();
		}
		if (statement instanceof IASTSwitchStatement) {
			mTemporarySymbolTable.beginScope();
		}
		if (statement instanceof IASTForStatement) {
			mTemporarySymbolTable.beginScope();
		}
		return super.visit(statement);
	}

	@Override
	public int leave(final IASTStatement statement) {
		if (statement instanceof IASTCompoundStatement && !(statement.getParent() instanceof IASTFunctionDefinition
				|| statement.getParent() instanceof IASTForStatement)) {
			// the scope for IASTFunctionDefinition and IASTForStatement was //FIXME what about while, do, ..?
			// opened in parent before!
			mTemporarySymbolTable.endScope();
		}
		if (statement instanceof IASTSwitchStatement) {
			mTemporarySymbolTable.endScope();
		}
		if (statement instanceof IASTForStatement) {
			mTemporarySymbolTable.endScope();
		}
		return super.leave(statement);
	}

	/**
	 * For an IdentifierExpression just return the identifier. For something like a struct access (s.a) return the
	 * identifier that designates the storage array used by the expression (here: s).
	 *
	 */
	private String extractExpressionId(final IASTNode expression) {
		if (expression instanceof IASTIdExpression) {
			final String id = ((IASTIdExpression) expression).getName().toString();
			return mSymTab.applyMultiparseRenaming(expression.getContainingFilename(), id);
		}
		if (expression instanceof IASTFieldReference && !((IASTFieldReference) expression).isPointerDereference()) {
			return extractExpressionId(((IASTFieldReference) expression).getFieldOwner());
		}
		if (expression instanceof IASTArraySubscriptExpression) {
			return extractExpressionId(((IASTArraySubscriptExpression) expression).getArrayExpression());
		}
		if (expression instanceof IASTUnaryExpression) {
			final IASTUnaryExpression unary = (IASTUnaryExpression) expression;
			if (unary.getOperator() == IASTUnaryExpression.op_bracketedPrimary) {
				return extractExpressionId(unary.getOperand());
			}
		}
		return null;
	}

	private void addNameOfNonFunctionDeclarator(final IASTDeclarator d) {
		if (!(d instanceof IASTFunctionDeclarator)) {
			final String key = d.getName().toString();
			final String rslvKey = mSymTab.applyMultiparseRenaming(d.getContainingFilename(), key);
			mTemporarySymbolTable.put(rslvKey, d);
		}
	}

	private void addFunction(final String id, final String filename) {
		// Rename the ID according to multiparse rules
		final String rslvdId = mSymTab.applyMultiparseRenaming(filename, id);
		// check if id is the name of a function and not shadowed here
		final IASTNode function = mFunctionTable.get(rslvdId);
		if (function != null) {
			mFunctions.add(rslvdId);
		}
	}
}
