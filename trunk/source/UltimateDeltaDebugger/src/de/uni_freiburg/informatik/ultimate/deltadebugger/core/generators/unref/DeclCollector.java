package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.unref;

import java.util.Arrays;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import org.eclipse.cdt.core.dom.ast.ASTNodeProperty;
import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclarationStatement;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.ASTNodeUtils;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.CommaSeparatedChildFinder;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.TokenCollector;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.TokenCollector.Token;

class DeclCollector extends LeadingNodeCollector {
	private final Set<DeclFlag> mOptions;
	private List<DeclParts> mResult;

	public DeclCollector(Set<DeclFlag> options, List<DeclParts> result) {
		mOptions = options;
		mResult = result;
	}

	private boolean isSupportedDeclaration(final IASTSimpleDeclaration declaration) {
		// Prototypes are handled together with functions, no declarators means nothing to delete
		if (ASTNodeUtils.isFunctionPrototype(declaration) || declaration.getDeclarators().length == 0) {
			return false;
		}

		// Filter type (typedef or not)
		final boolean isTypedef = ASTNodeUtils.isTypedef(declaration);
		if ((isTypedef && !mOptions.contains(DeclFlag.TYPEDEFS))
				|| (!isTypedef && !mOptions.contains(DeclFlag.VARS))) {
			return false;
		}

		// Filter scope (global, local or inside composite type)
		return isValidScope(declaration);
	}

	private boolean isValidScope(final IASTSimpleDeclaration declaration) {
		final ASTNodeProperty propertyInParent = declaration.getPropertyInParent();
		if (propertyInParent == IASTCompositeTypeSpecifier.MEMBER_DECLARATION && mOptions.contains(DeclFlag.MEMBERS)) {
			return true;
		}
		if (propertyInParent == IASTDeclarationStatement.DECLARATION && mOptions.contains(DeclFlag.LOCAL)) {
			return true;
		}
		if (propertyInParent == IASTTranslationUnit.OWNED_DECLARATION && mOptions.contains(DeclFlag.GLOBAL)) {
			return true;
		}
		// TODO: check what's left
		return false;
	}

	/**
	 * @param declSpecifier
	 *            decl specifier
	 * @return if the declSpecifier is a composite type or enum specifier that is referenced
	 */
	private boolean isReferencedTypeSpecifier(IASTDeclSpecifier declSpecifier) {
		if (declSpecifier instanceof IASTCompositeTypeSpecifier) {
			final IASTCompositeTypeSpecifier compositeTypeSpecifier = (IASTCompositeTypeSpecifier) declSpecifier;
			if (ASTNodeUtils.hasReferences(compositeTypeSpecifier.getName())) {
				return true;
			}
		} else if (declSpecifier instanceof IASTEnumerationSpecifier) {
			final IASTEnumerationSpecifier enumerationSpecifier = (IASTEnumerationSpecifier) declSpecifier;
			if (Arrays.stream(enumerationSpecifier.getEnumerators())
					.anyMatch(e -> ASTNodeUtils.hasReferences(e.getName()))
					|| ASTNodeUtils.hasReferences(enumerationSpecifier.getName())) {
				return true;
			}
		}
		return false;
	}

	/**
	 * @param node
	 *            pst node
	 * @param declSpecifier
	 *            declSpecifier
	 * @return list of tokens that need to be deleted from the given type specifier or null if not all tokens exist
	 */
	private Optional<List<Token>> getDeletableDeclSpecifierTokens(final IPSTRegularNode node,
			final IASTDeclSpecifier declSpecifier) {
		final List<Token> availableTokens = TokenCollector.collect(node);
		final List<Integer> requiredTokens = ASTNodeUtils.getRequiredDeclSpecifierTokens(declSpecifier);
		final List<Token> deletableTokens = availableTokens.stream().filter(t -> requiredTokens.contains(t.getType()))
				.collect(Collectors.toList());
		if (deletableTokens.size() == requiredTokens.size()) {
			return Optional.of(deletableTokens);
		}
		return Optional.empty();
	}

	private List<IPSTNode> getUnreferencedDeclarators(IPSTRegularNode node, IASTSimpleDeclaration declaration) {
		return Arrays.stream(declaration.getDeclarators()).filter(d -> !ASTNodeUtils.hasReferences(d))
				.map(node::findRegularChild).filter(Objects::nonNull).collect(Collectors.toList());
	}

	@Override
	protected int visitRegular(IPSTRegularNode node) {
		if (!(node.getAstNode() instanceof IASTSimpleDeclaration)) {
			return PROCESS_CONTINUE;
		}
		final IASTSimpleDeclaration declaration = (IASTSimpleDeclaration) node.getAstNode();
		if (!isSupportedDeclaration(declaration)) {
			return PROCESS_CONTINUE;
		}

		// Check if there is a referenced type specifier, which cannot be removed even if all declarators are
		// unreferenced
		final IASTDeclSpecifier declSpecifier = declaration.getDeclSpecifier();
		final IASTDeclSpecifier referencedTypeSpecifier = isReferencedTypeSpecifier(declSpecifier) ? declSpecifier
				: null;
		// Get the tokens that need to be removed in order to keep the type specifier individually
		final IPSTRegularNode declSpecifierNode = node.findRegularChild(declSpecifier);
		List<Token> typeSpecifierTokens = null;
		if (referencedTypeSpecifier != null && declSpecifierNode != null) {
			typeSpecifierTokens = getDeletableDeclSpecifierTokens(declSpecifierNode, declSpecifier).orElse(null);
		}
		mResult.add(new DeclParts(node, CommaSeparatedChildFinder.run(node, IASTSimpleDeclaration.DECLARATOR),
				getUnreferencedDeclarators(node, declaration), referencedTypeSpecifier, typeSpecifierTokens,
				getFilteredLeadingMacroExpansions(mOptions.contains(DeclFlag.INCLUDE_EMPTY_MACROS),
						mOptions.contains(DeclFlag.INCLUDE_EXTENSION_MACRO))));
		return PROCESS_SKIP;
	}
}