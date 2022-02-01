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

import java.util.List;

import org.eclipse.cdt.core.dom.ast.ASTNodeProperty;
import org.eclipse.cdt.core.dom.ast.IASTArrayModifier;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTCastExpression;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarationStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTDoStatement;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEqualsInitializer;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTExpressionList;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTInitializerList;
import org.eclipse.cdt.core.dom.ast.IASTLabelStatement;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTPointerOperator;
import org.eclipse.cdt.core.dom.ast.IASTStandardFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTTypeId;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;
import org.eclipse.cdt.core.dom.ast.c.ICASTDesignatedInitializer;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes.ChangeCollector;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTACSLNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTConditionalBlock;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.ASTNodeConsumerDispatcher;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.IASTNodeConsumer;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.RewriteUtils;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ContractStatement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LogicStatement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopStatement;

/**
 * A delta debugger strategy that skips some of the problematic transformations of the aggressive strategy. It doesn't
 * remove function parameters, pointer operators and does not change types. It also doesn't try multiple alternative
 * replacements for expressions.
 */
public class SafeStrategy implements IHddStrategy {
	@SuppressWarnings("squid:S1698")
	@Override
	public void createAdditionalChangesForExpandedNode(final IPSTNode node, final ChangeCollector collector) {
		// Add a change to remove the inactive parts of the conditional block
		if (node instanceof IPSTConditionalBlock) {
			collector.addDeleteConditionalDirectivesChange((IPSTConditionalBlock) node);
		}
		
		// Add a change to delete the operator of unary expressions
		final IASTNode astNode = node.getAstNode();
		if (astNode instanceof IASTUnaryExpression) {
			collector.addDeleteAllTokensChange(node);
		}

		if (astNode instanceof IASTIfStatement) {
			collector.addDeleteIfStatementTokensChange((IPSTRegularNode) node, (IASTIfStatement) astNode);
		}
		if (astNode instanceof IASTForStatement) {
			collector.addDeleteForStatementTokensChange((IPSTRegularNode) node, (IASTForStatement) astNode);
		}
		if (astNode instanceof IASTWhileStatement) {
			collector.addDeleteWhileStatementTokensChange((IPSTRegularNode) node, (IASTWhileStatement) astNode);
		}

		if (astNode instanceof IASTDoStatement) {
			collector.addDeleteDoStatementTokensChange((IPSTRegularNode) node);
		}

		if (astNode instanceof IASTCompoundStatement
				&& astNode.getPropertyInParent() == IASTCompoundStatement.NESTED_STATEMENT) {
			collector.addDeleteAllTokensChange(node);
		}
	}
	
	@Override
	public void createChangeForNode(final IPSTNode node, final ChangeCollector collector) {
		if (node instanceof IPSTRegularNode) {
			RegularNodeHandler.invoke((IPSTRegularNode) node, collector);
		} else if (node instanceof IPSTConditionalBlock) {
			// Only delete full blocks if they are on the top level or inside
			// compound statements
			// This is one way to prevent rewrite conflicts caused by deleting
			// tokens inside nested conditional blocks and the blocks at the
			// same time
			final IPSTRegularNode regularParent = node.getRegularParent();
			if (regularParent instanceof IPSTTranslationUnit
					|| regularParent.getAstNode() instanceof IASTCompoundStatement) {
				collector.addDeleteChange(node);
			}
		} else if (node instanceof IPSTACSLNode) {
			final IPSTACSLNode acslNode = (IPSTACSLNode) node;
			if (acslNode.getAcslNode() instanceof ContractStatement || acslNode.getAcslNode() instanceof LoopStatement
					|| acslNode.getAcslNode() instanceof LogicStatement) {
				// Delete statements, nothing else
				collector.addDeleteChange(node);
			}
		} else {
			// delete every preprocessor node
			collector.addDeleteChange(node);
		}
	}
	
	@Override
	public boolean expandUnchangeableNodeImmediately(final IPSTNode node) {
		return node instanceof IPSTConditionalBlock;
	}

	/**
	 * Regular node handler.
	 */
	static final class RegularNodeHandler implements IASTNodeConsumer {
		private final IPSTRegularNode mCurrentNode;
		
		private final ChangeCollector mCollector;
		
		/**
		 * @param node
		 *            Node.
		 * @param collector
		 *            collector of changes
		 */
		private RegularNodeHandler(final IPSTRegularNode node, final ChangeCollector collector) {
			mCurrentNode = node;
			mCollector = collector;
		}
		
		@SuppressWarnings("squid:S1698")
		static void invoke(final IPSTRegularNode node, final ChangeCollector collector) {
			final IASTNode astNode = node.getAstNode();
			final ASTNodeProperty propertyInParent = astNode.getPropertyInParent();

			// Do not delete function parameters. Call Arguments are handled like normal expressions.
			// Delete everything else is comma separated (expressions are handled below)
			if (propertyInParent == IASTStandardFunctionDeclarator.FUNCTION_PARAMETER) {
				return;
			} else if (propertyInParent == IASTInitializerList.NESTED_INITIALIZER
					|| propertyInParent == ICASTDesignatedInitializer.OPERAND) {
				collector.addDeleteWithCommaChange(node, true);
				return;
			} else if (propertyInParent == IASTEnumerationSpecifier.ENUMERATOR) {
				collector.addDeleteWithCommaChange(node, false);
				return;
			}
			
			new ASTNodeConsumerDispatcher(new RegularNodeHandler(node, collector)).dispatch(astNode);
		}
		
		@Override
		public void on(final IASTArrayModifier arrayModifier) {
			// Removing the brackets from an array declaration (that could not be removed itself)
			// should have a very low probability to still type check, so better don't do this.
		}
		
		@SuppressWarnings("squid:S1698")
		@Override
		public void on(final IASTDeclaration declaration) {
			
			// The declaration is usually the same as the parent statement without the ";"
			if (declaration.getPropertyInParent() == IASTDeclarationStatement.DECLARATION) {
				return;
			}
			
			IASTNodeConsumer.super.on(declaration);
		}
		
		@Override
		public void on(final IASTDeclarator declarator) {
			// includes function/variable/whatever name and additional syntax that
			// cannot be deleted alone
		}
		
		@Override
		public void on(final IASTDeclSpecifier declSpecifier) {
			// Too many type checking errors if we change it.
			// Of course, it should be possible to simplify it, replace macros and
			// type qualifiers
		}
		
		@Override
		public void on(final IASTEqualsInitializer equalsInitializer) {
			// We don't want to create uninitialized variables (and thus undefined behavior), so always keep equals
			// initializer.
			
			// The only exception are variables with static storage, these are zero initialized implicitly.
			// In such a case the initializer could be deleted.
			// TODO: actually implement the idea above: need to get the corresponding IASTDeclaration and then check the
			// storage class.
		}
		
		@SuppressWarnings("squid:S1698")
		@Override
		public void on(final IASTExpression expression) {
			final ASTNodeProperty property = expression.getPropertyInParent();
			
			// delete the function name from function calls, leaving an expression
			// list
			// Note that this may cause subsequent compilation errors, because the
			// last element of that expression list may be deleted (since it is
			// considered to be a function call argument list)
			if (property == IASTFunctionCallExpression.FUNCTION_NAME) {
				mCollector.addDeleteChange(mCurrentNode);
				return;
			}
			
			// Probably not a good idea to generate infinite loops, but these are
			// one of the few expressions that can be deleted without causing syntax
			// errors.
			if (property == IASTForStatement.CONDITION || property == IASTForStatement.ITERATION) {
				mCollector.addDeleteChange(mCurrentNode);
				return;
			}

			final List<String> allReplacements = RewriteUtils.removeEquivalentReplacements(mCurrentNode,
					RewriteUtils.getMinimalExpressionReplacements(expression));

			// Do not try multiple alternatives to not waste time
			final List<String> replacements = allReplacements.subList(0, allReplacements.isEmpty() ? 0 : 1);
			
			// Binary expression operands are deleted or replaced
			if (property == IASTBinaryExpression.OPERAND_ONE || property == IASTBinaryExpression.OPERAND_TWO) {
				mCollector.addDeleteBinaryExpressionOperandChange(mCurrentNode, replacements);
				return;
			}

			// Comma separated expressions can be deleted as well
			if (property == IASTExpressionList.NESTED_EXPRESSION) {
				mCollector.addDeleteWithCommaOrReplaceChange(mCurrentNode, true, replacements);
				return;
			}
			
			if (!replacements.isEmpty()) {
				mCollector.addMultiReplaceChange(mCurrentNode, replacements);
			}
		}
		
		@Override
		public void on(final IASTInitializerList initializerList) {
			// An empty initializer list is not valid C syntax (see C grammar).
			// Unfortunately putting a "0" as single element only works if the first
			// member of
			// is a scalar type. If it isn't, or the struct is empty, this will not
			// compile.
			// Since gcc accepts "{}" and the deletion of individual elements will
			// eventually create
			// an empty list anyways, we can directly try that.
			// Note that deleting the whole initializer list would often result in
			// syntax errors,
			// because the "=" token remains and we don't want to have uninitialized
			// variables anyways.
			mCollector.addReplaceChange(mCurrentNode, "{}");
		}
		
		@Override
		public void on(final IASTName name) {
			// no point in messing with names
		}
		
		@Override
		public void on(final IASTNode node) {
			// Unless overridden regular nodes are simply deleted
			mCollector.addDeleteChange(mCurrentNode);
		}
		
		@Override
		public void on(final IASTPointerOperator pointerOperator) {
			// removing a pointer operator appears to be a bad idea, because of
			// compilation errors.
			// could try to remove specifiers, like const, restrict etc. though.
		}
		
		@Override
		public void on(final IASTStatement statement) {
			// delete all statements (if required replace by ";")
			mCollector.addReplaceChange(mCurrentNode, RewriteUtils.getReplacementStringForSafeDeletion(mCurrentNode));
		}
		
		@SuppressWarnings("squid:S1698")
		@Override
		public void on(final IASTTypeId typeId) {
			// Delete typeid and parenthesis from cast expression
			if (typeId.getPropertyInParent() == IASTCastExpression.TYPE_ID) {
				mCollector.addDeleteTypeIdFromCastExpressionChange(mCurrentNode);
			}
		}
	}
}
