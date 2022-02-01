package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.unref;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTMacroExpansion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.ASTNodeUtils;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.CommaSeparatedChild;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.TokenCollector.Token;

class DeclParts {
	private final IPSTNode mDeclaration;
	private final List<CommaSeparatedChild> mAllDeclarators;
	private final List<IPSTNode> mUnreferencedDeclarators;
	private final IASTDeclSpecifier mReferencedTypeSpecifier;
	private final List<Token> mTypeSpecifierTokens;
	private final List<IPSTMacroExpansion> mLeadingMacroExpansions;

	public DeclParts(IPSTNode declaration, List<CommaSeparatedChild> allDeclarators,
			List<IPSTNode> unreferencedDeclarators, IASTDeclSpecifier referencedTypeSpecifier,
			List<Token> typeSpecifierTokens, List<IPSTMacroExpansion> leadingMacroExpansions) {
		mDeclaration = declaration;
		mAllDeclarators = allDeclarators;
		mUnreferencedDeclarators = unreferencedDeclarators;
		mReferencedTypeSpecifier = referencedTypeSpecifier;
		mTypeSpecifierTokens = typeSpecifierTokens;
		mLeadingMacroExpansions = leadingMacroExpansions;
	}

	public IPSTNode getDeclaration() {
		return mDeclaration;
	}

	public List<CommaSeparatedChild> getAllDeclarators() {
		return mAllDeclarators;
	}

	public List<IPSTNode> getUnreferencedDeclarators() {
		return mUnreferencedDeclarators;
	}

	public IASTDeclSpecifier getReferencedTypeSpecifier() {
		return mReferencedTypeSpecifier;
	}

	public List<Token> getTypeSpecifierTokens() {
		return mTypeSpecifierTokens;
	}

	public List<IPSTMacroExpansion> getLeadingMacroExpansions() {
		return mLeadingMacroExpansions;
	}

	public IASTSimpleDeclaration getAstDeclaration() {
		return (IASTSimpleDeclaration) mDeclaration.getAstNode();
	}

	public boolean hasReferencedTypeSpecifier() {
		return mReferencedTypeSpecifier != null;
	}

	public boolean anyDeclaratorUnreferenced() {
		return !mUnreferencedDeclarators.isEmpty();
	}

	public boolean allDeclaratorsUnreferenced() {
		return mUnreferencedDeclarators.size() == mAllDeclarators.size();
	}

	public String getTypeSpecifierName() {
		final IASTDeclSpecifier declSpecifier = getAstDeclaration().getDeclSpecifier();
		if (declSpecifier instanceof IASTCompositeTypeSpecifier) {
			return ((IASTCompositeTypeSpecifier) declSpecifier).getName().toString();
		}
		if (declSpecifier instanceof IASTEnumerationSpecifier) {
			return ((IASTEnumerationSpecifier) declSpecifier).getName().toString();
		}
		return "";
	}

	public List<String> getAllDeclaratorNames() {
		return getDeclaratorNames(mAllDeclarators.stream().map(CommaSeparatedChild::astNode));
	}

	public List<String> getReferencedDeclaratorNames() {
		final Set<IASTNode> unreferencedNodes = mUnreferencedDeclarators.stream().map(IPSTNode::getAstNode)
				.collect(Collectors.toSet());
		return getDeclaratorNames(mAllDeclarators.stream().filter(n -> !unreferencedNodes.contains(n.astNode()))
				.map(CommaSeparatedChild::astNode));
	}

	public List<String> getUnreferencedDeclaratorNames() {
		return getDeclaratorNames(mUnreferencedDeclarators.stream().map(IPSTNode::getAstNode));
	}

	private static List<String> getDeclaratorNames(Stream<IASTNode> s) {
		return s.map(n -> ASTNodeUtils.getNestedDeclaratorName((IASTDeclarator) n).toString())
				.collect(Collectors.toList());
	}
}
