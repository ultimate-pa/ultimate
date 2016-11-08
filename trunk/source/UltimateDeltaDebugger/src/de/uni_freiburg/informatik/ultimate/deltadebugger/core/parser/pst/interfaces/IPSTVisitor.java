package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces;

import org.eclipse.cdt.core.dom.ast.ASTVisitor;

public interface IPSTVisitor {
	int PROCESS_SKIP = ASTVisitor.PROCESS_SKIP;
	int PROCESS_ABORT = ASTVisitor.PROCESS_ABORT;
	int PROCESS_CONTINUE = ASTVisitor.PROCESS_CONTINUE;

	default int defaultLeave(final IPSTNode node) {
		return PROCESS_CONTINUE;
	}

	default int defaultVisit(final IPSTNode node) {
		return PROCESS_CONTINUE;
	}

	default int leave(final IPSTComment comment) {
		return defaultLeave(comment);
	}

	default int leave(final IPSTConditionalBlock conditionalBlock) {
		return defaultLeave(conditionalBlock);
	}

	default int leave(final IPSTDirective directive) {
		return defaultLeave(directive);
	}

	default int leave(final IPSTIncludeDirective include) {
		return defaultLeave(include);
	}

	default int leave(final IPSTLiteralRegion literalRegion) {
		return PROCESS_SKIP;
	}

	default int leave(final IPSTMacroExpansion expansion) {
		return defaultLeave(expansion);
	}

	default int leave(final IPSTRegularNode node) {
		return defaultLeave(node);
	}

	default int leave(final IPSTTranslationUnit tu) {
		return defaultLeave(tu);
	}

	default int visit(final IPSTComment comment) {
		return defaultVisit(comment);
	}

	default int visit(final IPSTConditionalBlock conditionalBlock) {
		return defaultVisit(conditionalBlock);
	}

	default int visit(final IPSTDirective directive) {
		return defaultVisit(directive);
	}

	default int visit(final IPSTIncludeDirective include) {
		return defaultVisit(include);
	}

	default int visit(final IPSTLiteralRegion literalRegion) {
		return PROCESS_SKIP;
	}

	default int visit(final IPSTMacroExpansion expansion) {
		return defaultVisit(expansion);
	}

	default int visit(final IPSTRegularNode node) {
		return defaultVisit(node);
	}

	default int visit(final IPSTTranslationUnit tu) {
		return defaultVisit(tu);
	}

}
