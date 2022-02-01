/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd;

import java.util.EnumSet;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.ASTNodeProperty;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclarationStatement;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorMacroDefinition;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes.ChangeCollector;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.ASTNodeUtils;

/**
 * A strategy to delete unreferenced things only.
 * A slightly better solution would be to create a dedicated VariantGenerator/Pass that can delete all declarations of
 * the same name, e.g. forward declarations and also function definition and all prototypes.
 */
public class UnreferencedStrategy implements IHddStrategy {
	
	/**
	 * Specifies what kind of names to delete.
	 */
	public enum Kind {
		/**
		 * Function definition.
		 */
		FUNCTION_DEF,
		/**
		 * Global declaration.
		 */
		GLOBAL_DECL,
		/**
		 * Local declaration.
		 */
		LOCAL_DECL,
		/**
		 * Other declaration.
		 */
		OTHER_DECL,
		/**
		 * Macro definition.
		 */
		MAKRO_DEF;
	}
	
	private final Set<Kind> mKinds;
	
	/**
	 * Constructor using all {@link Kind}s.
	 */
	public UnreferencedStrategy() {
		this(EnumSet.allOf(Kind.class));
	}
	
	/**
	 * @param kinds
	 *            Kinds of names to delete.
	 */
	public UnreferencedStrategy(final Set<Kind> kinds) {
		mKinds = EnumSet.copyOf(kinds);
	}
	
	@Override
	public void createChangeForNode(final IPSTNode node, final ChangeCollector collector) {
		final IASTNode astNode = node.getAstNode();
		if (!isUnreferencedNodeToDelete(astNode)) {
			return;
		}
		if (isStatementRequired(astNode)) {
			collector.addReplaceChange(node, ";");
		} else {
			collector.addDeleteChange(node);
		}
	}
	
	@SuppressWarnings("squid:S1698")
	private static boolean isStatementRequired(final IASTNode astNode) {
		final ASTNodeProperty property = astNode.getPropertyInParent();
		if (property == IASTForStatement.INITIALIZER) {
			return true;
		}
		if (property == IASTTranslationUnit.OWNED_DECLARATION) {
			return false;
		}
		if (property == IASTDeclarationStatement.DECLARATION) {
			return ((IASTDeclarationStatement) astNode.getParent())
					.getPropertyInParent() != IASTCompoundStatement.NESTED_STATEMENT;
		}
		// TODO: find out what's left and handle it accordingly
		return false;
	}
	
	private boolean isUnreferencedNodeToDelete(final IASTNode astNode) {
		if (astNode instanceof IASTSimpleDeclaration && mKinds.contains(getDeclKind(astNode))) {
			return !ASTNodeUtils.hasReferences((IASTSimpleDeclaration) astNode);
		} else if (astNode instanceof IASTFunctionDefinition && mKinds.contains(Kind.FUNCTION_DEF)) {
			return !ASTNodeUtils.hasReferences((IASTFunctionDefinition) astNode);
		} else if (astNode instanceof IASTPreprocessorMacroDefinition && mKinds.contains(Kind.MAKRO_DEF)) {
			return !ASTNodeUtils.hasReferences((IASTPreprocessorMacroDefinition) astNode);
		}
		return false;
	}
	
	@SuppressWarnings("squid:S1698")
	private static Kind getDeclKind(final IASTNode astNode) {
		final ASTNodeProperty property = astNode.getPropertyInParent();
		if (property == IASTTranslationUnit.OWNED_DECLARATION) {
			return Kind.GLOBAL_DECL;
		}
		if (property == IASTDeclarationStatement.DECLARATION) {
			return Kind.LOCAL_DECL;
		}
		return Kind.OTHER_DECL;
	}
	
	@Override
	public boolean expandUnchangeableNodeImmediately(final IPSTNode node) {
		return true;
	}
}
