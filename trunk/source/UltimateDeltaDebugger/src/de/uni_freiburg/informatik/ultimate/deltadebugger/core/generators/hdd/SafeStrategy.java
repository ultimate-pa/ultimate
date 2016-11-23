package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd;

import java.util.List;

import org.eclipse.cdt.core.dom.ast.ASTGenericVisitor;
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
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTProtectedRegion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.ASTNodeConsumerDispatcher;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.IASTNodeConsumer;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.RewriteUtils;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ContractStatement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LogicStatement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopStatement;

/**
 * A safer delta debugger strategy.
 */
public class SafeStrategy implements IHddStrategy {
	@Override
	public void createAdditionalChangesForExpandedNode(final IPSTNode node, final ChangeCollector collector) {
		// Add a change to remove the inactive parts of the conditional block
		if (node instanceof IPSTConditionalBlock) {
			collector.addDeleteConditionalDirectivesChange((IPSTConditionalBlock) node);
		}
		
		// Add a change to delete the operator of unary expressions
		if (node.getASTNode() instanceof IASTUnaryExpression) {
			collector.addDeleteAllTokensChange(node);
		}
		
		if (node.getASTNode() instanceof IASTIfStatement) {
			collector.addDeleteIfStatementTokensChange((IPSTRegularNode) node, (IASTIfStatement) node.getASTNode());
		}
		if (node.getASTNode() instanceof IASTForStatement) {
			collector.addDeleteForStatementTokensChange((IPSTRegularNode) node, (IASTForStatement) node.getASTNode());
		}
		if (node.getASTNode() instanceof IASTWhileStatement) {
			collector.addDeleteWhileStatementTokensChange((IPSTRegularNode) node,
					(IASTWhileStatement) node.getASTNode());
		}
		
		if (node.getASTNode() instanceof IASTDoStatement) {
			collector.addDeleteDoStatementTokensChange((IPSTRegularNode) node);
		}
		
		if (node.getASTNode() instanceof IASTCompoundStatement
				&& node.getASTNode().getPropertyInParent() == IASTCompoundStatement.NESTED_STATEMENT) {
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
					|| regularParent.getASTNode() instanceof IASTCompoundStatement) {
				collector.addDeleteChange(node);
			}
		} else if (node instanceof IPSTACSLNode) {
			final IPSTACSLNode acslNode = (IPSTACSLNode) node;
			if (acslNode.getACSLNode() instanceof ContractStatement || acslNode.getACSLNode() instanceof LoopStatement
					|| acslNode.getACSLNode() instanceof LogicStatement) {
				// Delete statements, nothing else
				collector.addDeleteChange(node);
			}
		} else {
			// delete every preprocessor node
			collector.addDeleteChange(node);
		}
	}
	
	@Override
	public boolean expandIntoOwnGroup(final IPSTNode node) {
		return false;
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
		 * @param node Node.
		 * @param collector collector of changes
		 */
		private RegularNodeHandler(final IPSTRegularNode node, final ChangeCollector collector) {
			mCurrentNode = node;
			mCollector = collector;
		}
		
		static void invoke(final IPSTRegularNode node, final ChangeCollector collector) {
			final IASTNode astNode = node.getASTNode();
			final ASTNodeProperty propertyInParent = astNode.getPropertyInParent();

			// Delete everything that is known to be comma separated accordingly
			if (propertyInParent == IASTExpressionList.NESTED_EXPRESSION
					|| propertyInParent == IASTInitializerList.NESTED_INITIALIZER
					|| propertyInParent == ICASTDesignatedInitializer.OPERAND) {
					// TODO: add check for referenced function before deleting parameters/arguments
				collector.addDeleteWithCommaChange(node, true);
				return;
			} else if (propertyInParent == IASTStandardFunctionDeclarator.FUNCTION_PARAMETER
					|| propertyInParent == IASTFunctionCallExpression.ARGUMENT
					|| propertyInParent == IASTEnumerationSpecifier.ENUMERATOR) {
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

			final List<String> replacements = RewriteUtils.getMinimalExpressionReplacements(expression);

			// Binary expression operands are deleted or replaced
			if (property == IASTBinaryExpression.OPERAND_ONE || property == IASTBinaryExpression.OPERAND_TWO) {
				mCollector.addDeleteBinaryExpressionOperandChange(mCurrentNode, replacements);
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
			// delete statements inside compound statements
			if (statement.getPropertyInParent() == IASTCompoundStatement.NESTED_STATEMENT) {
				mCollector.addDeleteChange(mCurrentNode);
				return;
			}
			
			// delete statements after a label
			if (statement.getPropertyInParent() == IASTLabelStatement.NESTED_STATEMENT) {
				mCollector.addDeleteChange(mCurrentNode);
				return;
			}
			
			mCollector.addReplaceChange(mCurrentNode, ";");
		}
		
		@Override
		public void on(final IASTTypeId typeId) {
			// Delete typeid and parenthesis from cast expression
			if (typeId.getPropertyInParent() == IASTCastExpression.TYPE_ID) {
				mCollector.addDeleteTypeIdFromCastExpressionChange(mCurrentNode);
			}
		}
	}
}
