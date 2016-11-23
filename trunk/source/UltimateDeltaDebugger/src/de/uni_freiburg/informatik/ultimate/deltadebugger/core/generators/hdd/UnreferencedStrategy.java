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
 * 
 * A slightly better solution would be to create a dedicated VariantGenerator/Pass that can delete all declarations of
 * the same name, e.g. forward declarations and also function definition and all prototypes.
 */
public class UnreferencedStrategy implements IHddStrategy {

	/**
	 * Specifies what kind of names to delete.
	 */
	public enum Kind {
		FUNCTION_DEF, GLOBAL_DECL, LOCAL_DECL, OTHER_DECL, MAKRO_DEF;
	}

	private final Set<Kind> mKinds;

	public UnreferencedStrategy() {
		this(EnumSet.allOf(Kind.class));
	}

	public UnreferencedStrategy(final Set<Kind> kinds) {
		mKinds = EnumSet.copyOf(kinds);
	}

	@Override
	public void createChangeForNode(final IPSTNode node, final ChangeCollector collector) {
		final IASTNode astNode = node.getASTNode();
		if (!isUnreferencedNodeToDelete(astNode)) {
			return;
		}
		if (isStatementRequired(astNode)) {
			collector.addReplaceChange(node, ";");
		} else {
			collector.addDeleteChange(node);
		}
	}

	private boolean isStatementRequired(IASTNode astNode) {
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

	private boolean isUnreferencedNodeToDelete(IASTNode astNode) {
		if (astNode instanceof IASTSimpleDeclaration && mKinds.contains(getDeclKind(astNode))) {
			return !ASTNodeUtils.hasReferences((IASTSimpleDeclaration) astNode);
		} else if (astNode instanceof IASTFunctionDefinition && mKinds.contains(Kind.FUNCTION_DEF)) {
			return !ASTNodeUtils.hasReferences((IASTFunctionDefinition) astNode);
		} else if (astNode instanceof IASTPreprocessorMacroDefinition && mKinds.contains(Kind.MAKRO_DEF)) {
			return !ASTNodeUtils.hasReferences((IASTPreprocessorMacroDefinition) astNode);
		}
		return false;
	}

	private Kind getDeclKind(IASTNode astNode) {
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
