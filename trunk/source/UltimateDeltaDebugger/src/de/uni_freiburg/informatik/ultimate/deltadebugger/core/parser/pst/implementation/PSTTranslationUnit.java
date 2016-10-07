package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation;

import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

public class PSTTranslationUnit extends PSTRegularNode implements IPSTTranslationUnit {
	
	public PSTTranslationUnit(ISourceDocument source, ISourceRange location, IASTTranslationUnit tu) {
		super(source, location, tu);
	}

	@Override
	public IASTTranslationUnit getASTNode() {
		return (IASTTranslationUnit) astNode;
	}

	@Override
	int dispatchVisit(IPSTVisitor action) {
		return action.visit(this);
	}
	
	@Override
	int dispatchLeave(IPSTVisitor action) {
		return action.leave(this);
	}
	
}
