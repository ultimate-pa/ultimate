package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.unref;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTElaboratedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IBinding;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.ASTNodeUtils;

class BindingCollector extends LeadingNodeCollector {
	private final Set<ObjFlag> mOptions;
	private final Map<IBinding, List<IPSTNode>> mResult;

	BindingCollector(Set<ObjFlag> options, Map<IBinding, List<IPSTNode>> result) {
		mResult = result;
		mOptions = options;
	}

	private IBinding getUnreferencedBindingToDelete(IASTSimpleDeclaration declaration) {
		// Typedefs are handled differently because of multiple declarators and nested composite type specifiers
		// (which can occur anywhere but are much less likely)
		if (ASTNodeUtils.isTypedef(declaration)) {
			return null;
		}

		if (ASTNodeUtils.isFunctionPrototype(declaration)) {
			final IASTName name = ASTNodeUtils.getNestedDeclaratorName(declaration.getDeclarators()[0]);
			if (mOptions.contains(ObjFlag.PROTOTYPES) && !ASTNodeUtils.hasReferences(name)) {
				return name.resolveBinding();
			}
		}

		// plain type declaration (no typedef, no variable declarator, just struct, union or enum, maybe anonymous)
		if (declaration.getDeclarators().length == 0) {
			return getUnreferencedBindingFromDeclSpecifier(declaration.getDeclSpecifier());
		}
		return null;
	}

	private IBinding getUnreferencedBindingFromDeclSpecifier(IASTDeclSpecifier declSpecifier) {
		IASTName name = null;
		if (mOptions.contains(ObjFlag.COMPOSITES) && declSpecifier instanceof IASTCompositeTypeSpecifier) {
			name = ((IASTCompositeTypeSpecifier) declSpecifier).getName();
		} else if (mOptions.contains(ObjFlag.ENUMS) && declSpecifier instanceof IASTEnumerationSpecifier) {
			final IASTEnumerationSpecifier typeSpecifier = (IASTEnumerationSpecifier) declSpecifier;
			// All enumerators must be unreferenced as well...
			// TODO: do not consider references within the enum itself, e.g. enum { A, B, C = B + 1}; is not considered
			// unreferenced, because B is referenced
			if (Arrays.stream(typeSpecifier.getEnumerators())
					.allMatch(e -> !ASTNodeUtils.hasReferences(e.getName()))) {
				name = typeSpecifier.getName();
			}
		} else if (declSpecifier instanceof IASTElaboratedTypeSpecifier) {
			final IASTElaboratedTypeSpecifier typeSpecifier = (IASTElaboratedTypeSpecifier) declSpecifier;
			if ((mOptions.contains(ObjFlag.ENUMS) && typeSpecifier.getKind() == IASTElaboratedTypeSpecifier.k_enum)
					|| (mOptions.contains(ObjFlag.COMPOSITES)
							&& typeSpecifier.getKind() != IASTElaboratedTypeSpecifier.k_enum)) {
				name = typeSpecifier.getName();
			}
		}
		if (name != null && !ASTNodeUtils.hasReferences(name)) {
			return name.resolveBinding();
		}
		return null;
	}

	@Override
	public int visitRegular(final IPSTRegularNode node) {
		final IASTNode astNode = node.getAstNode();
		IBinding bindingToDelete = null;
		if (astNode instanceof IASTSimpleDeclaration) {
			bindingToDelete = getUnreferencedBindingToDelete((IASTSimpleDeclaration) astNode);
		} else if (astNode instanceof IASTFunctionDefinition) {
			final IASTName name = ASTNodeUtils
					.getNestedDeclaratorName(((IASTFunctionDefinition) astNode).getDeclarator());
			if (mOptions.contains(ObjFlag.FUNCDEFS) && !ASTNodeUtils.hasReferences(name)) {
				bindingToDelete = name.resolveBinding();
			}
		}
		if (bindingToDelete != null) {
			final List<IPSTNode> list = mResult.computeIfAbsent(bindingToDelete, s -> new ArrayList<>());
			if (mOptions.contains(ObjFlag.INCLUDE_ACSLCOMMENT) && getLeadingACSLComment() != null) {
				list.add(getLeadingACSLComment());
			}
			list.addAll(getFilteredLeadingMacroExpansions(mOptions.contains(ObjFlag.INCLUDE_EMPTY_MACROS),
					mOptions.contains(ObjFlag.INCLUDE_EXTENSION_MACRO)));
			list.add(node);
			return PROCESS_SKIP;
		}

		return PROCESS_CONTINUE;
	}
}
