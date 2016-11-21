package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst;

import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTACSLComment;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTACSLNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;

/**
 * Expands IPSTACSLComment nodes to contain IPSTACSLNodes where possible.
 *
 */
public final class PSTACSLBuilder implements IPSTVisitor {

	private final ILogger mLogger;
	/**
	 * Counter to detect if we are currently inside a function definition.
	 */
	private int mEnteredFunctionDefinitions;

	private PSTACSLBuilder(final ILogger logger) {
		mLogger = logger;
	}

	/**
	 * Expand all ACSL comments within the given PST node.
	 * 
	 * @param node
	 *            PST root node to expand nested ACSL comments in
	 * @param logger
	 *            logger
	 */
	public static void build(final IPSTNode node, final ILogger logger) {
		node.accept(new PSTACSLBuilder(logger));
	}

	@Override
	public int visit(IPSTACSLComment acslComment) {
		// Try to parse it, if it doesn't work just continue
		final ACSLCommentParser parser = new ACSLCommentParser(acslComment, mEnteredFunctionDefinitions < 1, mLogger);
		final IPSTACSLNode pstNode = parser.parseAndCreatePST();
		if (pstNode != null) {
			acslComment.addChild(pstNode);
		}
		return PROCESS_SKIP;
	}

	@Override
	public int visit(IPSTRegularNode node) {
		if (node.getASTNode() instanceof IASTFunctionDefinition) {
			++mEnteredFunctionDefinitions;
		}
		return PROCESS_CONTINUE;
	}

	@Override
	public int leave(IPSTRegularNode node) {
		if (node.getASTNode() instanceof IASTFunctionDefinition) {
			--mEnteredFunctionDefinitions;
		}
		return PROCESS_CONTINUE;
	}

}
