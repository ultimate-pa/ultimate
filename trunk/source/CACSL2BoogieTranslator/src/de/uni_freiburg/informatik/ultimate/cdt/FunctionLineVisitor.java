/**
 * This Visitor produces a HashMap with the Line-Ranges of
 * all Functions. This is necessary to determine the ACSL-Parser Mode.
 * This is global or local.
 */
package de.uni_freiburg.informatik.ultimate.cdt;

import java.util.HashMap;

import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;

/**
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @date 30.01.2012
 */
public class FunctionLineVisitor extends ASTVisitor {
	/**
	 * Map startline numbers of a block to end line numbers.
	 */
	private HashMap<Integer, Integer> lineRange;

	/**
	 * Standard Constructor.
	 */
	public FunctionLineVisitor() {
		this.lineRange = new HashMap<Integer, Integer>();
		this.shouldVisitDeclarations = true;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.cdt.core.dom.ast.ASTVisitor#visit(org.eclipse.cdt.core.dom
	 * .ast.IASTDeclaration)
	 */
	@Override
	public int visit(IASTDeclaration declaration) {
		if (declaration instanceof IASTFunctionDefinition) {
			IASTFunctionDefinition funcDef = (IASTFunctionDefinition) declaration;
			int start = funcDef.getFileLocation().getStartingLineNumber();
			int end = funcDef.getFileLocation().getEndingLineNumber();
			this.lineRange.put(start, end);
		}
		return PROCESS_CONTINUE;
	}

	/**
	 * Getter for the line range map, which maps startline numbers of blocks to
	 * their end line numbers.
	 * 
	 * @return <code>HashMap<Integer, Integer></code> the line ranges of all
	 *         functions
	 */
	public HashMap<Integer, Integer> getLineRange() {
		return lineRange;
	}

}
