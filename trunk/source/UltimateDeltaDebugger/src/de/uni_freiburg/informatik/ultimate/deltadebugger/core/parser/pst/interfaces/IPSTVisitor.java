package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces;

import org.eclipse.cdt.core.dom.ast.ASTVisitor;

public interface IPSTVisitor {
	public static final int PROCESS_SKIP = ASTVisitor.PROCESS_SKIP;
	public static final int PROCESS_ABORT = ASTVisitor.PROCESS_ABORT;
	public static final int PROCESS_CONTINUE = ASTVisitor.PROCESS_CONTINUE;
	
	default int defaultVisit(IPSTNode node) {
		return PROCESS_CONTINUE;
	}
	
	default int defaultLeave(IPSTNode node) {
		return PROCESS_CONTINUE;
	}
	
	default int visit(IPSTTranslationUnit tu) {
		return defaultVisit(tu);
	}
	
	default int visit(IPSTRegularNode node) {
		return defaultVisit(node);
	}
	
	default int visit(IPSTMacroExpansion expansion) {
		return defaultVisit(expansion);
	}

	default int visit(IPSTIncludeDirective include) {
		return defaultVisit(include);
	}
	
	default int visit(IPSTDirective directive) {
		return defaultVisit(directive);
	}
	
	default int visit(IPSTComment comment) {
		return defaultVisit(comment);
	}
	
	default int visit(IPSTConditionalBlock conditionalBlock) {
		return defaultVisit(conditionalBlock);
	}
	
	default int visit(IPSTLiteralRegion literalRegion) {
		return PROCESS_SKIP;
	}
	
	default int leave(IPSTTranslationUnit tu) {
		return defaultLeave(tu);
	}
	
	default int leave(IPSTRegularNode node) {
		return defaultLeave(node);
	}
	
	default int leave(IPSTMacroExpansion expansion) {
		return defaultLeave(expansion);
	}

	default int leave(IPSTIncludeDirective include) {
		return defaultLeave(include);
	}
	
	default int leave(IPSTDirective directive) {
		return defaultLeave(directive);
	}
	
	default int leave(IPSTComment comment) {
		return defaultLeave(comment);
	}
	
	default int leave(IPSTConditionalBlock conditionalBlock) {
		return defaultLeave(conditionalBlock);
	}
	
	default int leave(IPSTLiteralRegion literalRegion) {
		return PROCESS_SKIP;
	}
	
}